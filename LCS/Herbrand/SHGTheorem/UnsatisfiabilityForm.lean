import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.HerbrandTheorem
import Attach
import LCS.Herbrand.SHGTheorem.UnsatisfiabilityForm.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem

-- ===================================================================
-- Example 7.6.1 (companion type): ShgMotivPred
-- ===================================================================

/-- Example 7.6.1 (companion type): Predicate symbols for the
motivating example: P (unary) and R (binary). -/
@[blueprint "chap7__example_7_6_1"]
inductive ShgMotivPred : Type where
  | P : ShgMotivPred
  | R : ShgMotivPred

-- ===================================================================
-- Example 7.6.1 (companion type): ShgMotivConst
-- ===================================================================

/-- Example 7.6.1 (companion type): Constant symbols for the
motivating example: a. -/
@[blueprint "chap7__example_7_6_1"]
inductive ShgMotivConst : Type where
  | a : ShgMotivConst

-- ===================================================================
-- Example 7.6.1 (companion type): ShgMotivFunc
-- ===================================================================

/-- Example 7.6.1 (companion type): Function symbols for the motivating example: unary Skolem function f introduced to replace the existential quantifier exists y R(x, y). -/
@[blueprint "chap7__example_7_6_1"]
inductive ShgMotivFunc : Type where
  | f : ShgMotivFunc

-- ===================================================================
-- Example 7.6.1 (companion def): shgMotivLang
-- ===================================================================

/-- Example 7.6.1 (companion def): A language with predicates P (unary) and R (binary), constant a, and unary function symbol f (the Skolem function introduced in the example). SKOLEM-TO-EXISTENTIAL MAPPING (Def 7.6.2 (iv)): - `f : ShgMotivFunc` (arity 1) is the Skolem function introduced to replace the existential `∃y R(x, y)` appearing inside the NNF negation `shgMotivNNFNeg`. Its universal scope is `⟨x⟩` (single variable x = 0), hence arity 1. The term `f(x)` substitutes for y in the Skolemized formula `shgMotivSkolemized`. (A `SkolemSpec shgMotivLang_unSkolemized` bundle tying this symbol to the precise existential position would require a separate `shgMotivLangBase` without `f`, which the Example does not carry — instead the skolem symbol is included in the single `shgMotivLang` for expository simplicity.) -/
@[blueprint "chap7__example_7_6_1"]
def shgMotivLang : Language where
  funSymbols := ShgMotivFunc
  funArity := fun | .f => 1
  constSymbols := ShgMotivConst
  predSymbols := ShgMotivPred
  predArity := fun
    | .P => 1
    | .R => 2
  hasEquality := false

-- ===================================================================
-- Example 7.6.1 (helper): shgMotivVec1
-- ===================================================================

/-- Example 7.6.1 (companion def): Build a Fin 1 -> Term from a single
term in shgMotivLang. -/
@[blueprint "chap7__example_7_6_1"]
def shgMotivVec1 (t : Term shgMotivLang) :
    Fin 1 → Term shgMotivLang
  | ⟨0, _⟩ => t

-- ===================================================================
-- Example 7.6.1 (helper): shgMotivVec2
-- ===================================================================

/-- Example 7.6.1 (companion def): Build a Fin 2 -> Term from two terms
in shgMotivLang. -/
@[blueprint "chap7__example_7_6_1"]
def shgMotivVec2 (t1 t2 : Term shgMotivLang) :
    Fin 2 → Term shgMotivLang
  | ⟨0, _⟩ => t1
  | ⟨1, _⟩ => t2

-- ===================================================================
-- Example 7.6.1: shgMotivExFormula
-- ===================================================================

/-- Example 7.6.1: The formula A = exists x((P(x) or exists y R(x, y)) implies (exists z R(x, z) or P(a))). This formula motivates the SHG theorem by demonstrating the Skolemization process. The NNF of its negation B admits a G2nnf proof in normal form whose midsequent is quantifier-free, and the existential quantifier can be eliminated via the Skolem function f. Variables: x = 0, y = 1, z = 2. -/
@[blueprint "chap7__example_7_6_1"]
def shgMotivExFormula : FormulaN shgMotivLang :=
  FormulaN.ex 0
    (FormulaN.impl
      (FormulaN.disj
        (FormulaN.predN ShgMotivPred.P (shgMotivVec1 (.var 0)))
        (FormulaN.ex 1
          (FormulaN.predN ShgMotivPred.R
            (shgMotivVec2 (.var 0) (.var 1)))))
      (FormulaN.disj
        (FormulaN.ex 2
          (FormulaN.predN ShgMotivPred.R
            (shgMotivVec2 (.var 0) (.var 2))))
        (FormulaN.predN ShgMotivPred.P
          (shgMotivVec1 (.const ShgMotivConst.a)))))

-- ===================================================================
-- Example 7.6.1 (companion def): shgMotivNNFNeg
-- ===================================================================

/-- Example 7.6.1 (companion def): The NNF of the negation of A: B = forall x((P(x) or exists y R(x, y)) and (forall z not R(x, z) and not P(a))). Variables: x = 0, y = 1, z = 2. -/
@[blueprint "chap7__example_7_6_1"]
def shgMotivNNFNeg : FormulaN shgMotivLang :=
  FormulaN.all 0
    (FormulaN.conj
      (FormulaN.disj
        (FormulaN.predN ShgMotivPred.P (shgMotivVec1 (.var 0)))
        (FormulaN.ex 1
          (FormulaN.predN ShgMotivPred.R
            (shgMotivVec2 (.var 0) (.var 1)))))
      (FormulaN.conj
        (FormulaN.all 2
          (FormulaN.neg
            (FormulaN.predN ShgMotivPred.R
              (shgMotivVec2 (.var 0) (.var 2)))))
        (FormulaN.neg
          (FormulaN.predN ShgMotivPred.P
            (shgMotivVec1 (.const ShgMotivConst.a))))))

-- ===================================================================
-- Example 7.6.1 (companion def): shgMotivMidsequent
-- ===================================================================

/-- Example 7.6.1 (companion def): The midsequent formula (P(a) or R(a, y)) and (not R(a, y) and not P(a)). Variables: y = 1. -/
@[blueprint "chap7__example_7_6_1"]
def shgMotivMidsequent : FormulaN shgMotivLang :=
  FormulaN.conj
    (FormulaN.disj
      (FormulaN.predN ShgMotivPred.P
        (shgMotivVec1 (.const ShgMotivConst.a)))
      (FormulaN.predN ShgMotivPred.R
        (shgMotivVec2 (.const ShgMotivConst.a) (.var 1))))
    (FormulaN.conj
      (FormulaN.neg
        (FormulaN.predN ShgMotivPred.R
          (shgMotivVec2 (.const ShgMotivConst.a) (.var 1))))
      (FormulaN.neg
        (FormulaN.predN ShgMotivPred.P
          (shgMotivVec1 (.const ShgMotivConst.a)))))

-- ===================================================================
-- Example 7.6.1 (companion def): shgMotivSkolemized
-- ===================================================================

/-- Example 7.6.1 (companion def): The Skolemized sequent forall x((P(x) or R(x, f(x))) and (forall z not R(x, z) and not P(a))). The existential quantifier exists y R(x, y) is replaced by R(x, f(x)) using the unary Skolem function f. Variables: x = 0, z = 2. -/
@[blueprint "chap7__example_7_6_1"]
def shgMotivSkolemized : FormulaN shgMotivLang :=
  FormulaN.all 0
    (FormulaN.conj
      (FormulaN.disj
        (FormulaN.predN ShgMotivPred.P (shgMotivVec1 (.var 0)))
        (FormulaN.predN ShgMotivPred.R
          (shgMotivVec2 (.var 0)
            (Term.func ShgMotivFunc.f
              (shgMotivVec1 (.var 0))))))
      (FormulaN.conj
        (FormulaN.all 2
          (FormulaN.neg
            (FormulaN.predN ShgMotivPred.R
              (shgMotivVec2 (.var 0) (.var 2)))))
        (FormulaN.neg
          (FormulaN.predN ShgMotivPred.P
            (shgMotivVec1 (.const ShgMotivConst.a))))))

namespace ShgMotivProof
set_option backward.isDefEq.respectTransparency false
open LCS.FirstOrder.SemanticsN LCS.FirstOrder.Semantics.Subformulae

@[blueprint "chap7__example_7_6_1"]
abbrev F := FormulaN shgMotivLang

@[blueprint "chap7__example_7_6_1"]
abbrev a : Term shgMotivLang := .const ShgMotivConst.a

@[blueprint "chap7__example_7_6_1"]
abbrev p : F := .predN .P (shgMotivVec1 a)

@[blueprint "chap7__example_7_6_1"]
abbrev r (t : Term shgMotivLang) : F := .predN .R (shgMotivVec2 a t)

abbrev q : F := r (.var 1)

abbrev u : F := .all 2 (.neg (r (.var 2)))

abbrev e : F := .ex 1 (r (.var 1))

abbrev afterAll : F := .conj (.disj p q) (.conj u (.neg p))

abbrev afterEx : F := .conj (.disj p e) (.conj u (.neg p))

variable [DecidableEq F]

abbrev Tree (Γ : LCS.Finset F) :=
  G2nnfProofTree (by rfl : shgMotivLang.withoutEquality) Γ ∅

def castAnt {Γ Γ' : LCS.Finset F} (h : Γ = Γ') (t : Tree Γ) : Tree Γ' :=
  h ▸ t

theorem substVec1 (u t : Term shgMotivLang) (x : Nat) :
    (fun i => termSubst (shgMotivVec1 u i) t x) =
      shgMotivVec1 (termSubst u t x) := by
  funext i
  rcases i with ⟨i, hi⟩
  have h : i = 0 := by omega
  subst i
  rfl

theorem substVec2 (u v t : Term shgMotivLang) (x : Nat) :
    (fun i => termSubst (shgMotivVec2 u v i) t x) =
      shgMotivVec2 (termSubst u t x) (termSubst v t x) := by
  funext i
  rcases i with ⟨i, hi⟩
  by_cases h : i = 0
  · subst i; rfl
  · have h : i = 1 := by omega
    subst i; rfl

macro "shg_motiv_set" : tactic => `(tactic|
  ((try simp only [List.getElem_cons_zero, List.getElem_cons_succ, Prod.fst, Prod.snd]) <;>
   (apply LCS.Finset.ext; intro F
    simp [LCS.Finset.mem_insert, LCS.Finset.mem_ofList,
      LCS.Finset.mem_singleton, List.getElem_cons_zero, List.getElem_cons_succ,
      shgMotivMidsequent, shgMotivNNFNeg, afterAll, afterEx, p, q, r, u, e, a,
      shgMotivLang, formulaSubstN, substVec1, substVec2, termSubst,
      MaxQuantifierOccurrence.replace, or_assoc, or_left_comm, or_comm])))

macro "shg_motiv_side" : tactic => `(tactic|
  (refine ⟨?_, ?_, ?_, ?_⟩ <;>
   simp [G2nnfRuleCore.LogicalSideConditions, G2nnfRuleCore.conclusion,
     G2nnfRuleCore.premises, AllNNF, AllRectified,
     LCS.Finset.mem_insert, LCS.Finset.mem_ofList, LCS.Finset.mem_singleton,
     FormulaN.isNNF, isRectified, boundVarsFresh, distinctQuantifierBindings,
     formulaFVN, formulaBVN, termFV, isFreeForN, formulaSubstN, termSubst,
     MaxQuantifierOccurrence.replace, shgMotivMidsequent, shgMotivNNFNeg,
     afterAll, afterEx, p, q, r, u, e, a, shgMotivVec1, shgMotivVec2,
     Set.iUnion, Set.union, Set.inter, Set.diff, Set.singleton, Set.empty,
     Fin.exists_fin_succ, Fin.forall_fin_succ] <;>
   simp [Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
     shgMotivLang, termFV, shgMotivVec1, shgMotivVec2,
     Fin.exists_fin_succ, Fin.forall_fin_succ] <;> (intros; omega)))

def pAx : Tree (LCS.Finset.ofList [p, .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .axiomCompLeft p rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.axiom_ rule ⟨rfl, rfl⟩ rfl ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side

def rAx : Tree (LCS.Finset.ofList [q, .neg q]) := by
  let rule : G2nnfRuleCore shgMotivLang := .axiomCompLeft q rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.axiom_ rule ⟨rfl, rfl⟩ rfl ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side

def pWeak : Tree (LCS.Finset.ofList [p, .neg q, .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .weakLeft (.neg q) (LCS.Finset.ofList [p, .neg p]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side
  · refine castAnt ?_ pAx
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set

def rWeak : Tree (LCS.Finset.ofList [q, .neg q, .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .weakLeft (.neg p) (LCS.Finset.ofList [q, .neg q]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side
  · refine castAnt ?_ rAx
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set

def disjunction : Tree (LCS.Finset.ofList [.disj p q, .neg q, .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .disjLeft p q (LCS.Finset.ofList [.neg q, .neg p]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.twoPremise rule trivial rfl ?_ ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side
  · refine castAnt ?_ pWeak
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set
  · refine castAnt ?_ rWeak
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set

def innerConj1 : Tree (LCS.Finset.ofList [.disj p q, .conj (.neg q) (.neg p), .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .conjLeft1 (.neg q) (.neg p) (LCS.Finset.ofList [.disj p q, .neg p]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side
  · refine castAnt ?_ disjunction
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set

def innerConj2 : Tree (LCS.Finset.ofList [.disj p q, .conj (.neg q) (.neg p)]) := by
  let rule : G2nnfRuleCore shgMotivLang := .conjLeft2 (.neg q) (.neg p) (LCS.Finset.ofList [.disj p q, .conj (.neg q) (.neg p)]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side
  · refine castAnt ?_ innerConj1
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set

def outerConj1 : Tree (LCS.Finset.ofList [shgMotivMidsequent, .conj (.neg q) (.neg p)]) := by
  let rule : G2nnfRuleCore shgMotivLang := .conjLeft1 (.disj p q) (.conj (.neg q) (.neg p)) (LCS.Finset.ofList [.conj (.neg q) (.neg p)]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side
  · refine castAnt ?_ innerConj2
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set

def midTree : Tree (LCS.Finset.ofList [shgMotivMidsequent]) := by
  let rule : G2nnfRuleCore shgMotivLang := .conjLeft2 (.disj p q) (.conj (.neg q) (.neg p)) (LCS.Finset.ofList [shgMotivMidsequent]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side
  · refine castAnt ?_ outerConj1
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set

def universalInner : Tree (LCS.Finset.ofList [afterAll]) := by
  let rule : G2nnfRuleCore shgMotivLang := .allSubLeft afterAll (.conjRight (.disj p q) (.conjLeft (.all 2 (.neg (r (.var 2)))) (.neg p))) 2 (.neg (r (.var 2))) (.var 1) rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side
  · refine castAnt ?_ midTree
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set

def existential : Tree (LCS.Finset.ofList [afterEx]) := by
  let rule : G2nnfRuleCore shgMotivLang := .exSubLeft afterEx (.conjLeft (.disjRight p (.ex 1 (r (.var 1)))) (.conj u (.neg p))) 1 (r (.var 1)) 1 rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side
  · refine castAnt ?_ universalInner
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set

def originalTree : Tree (LCS.Finset.ofList [shgMotivNNFNeg]) := by
  let rule : G2nnfRuleCore shgMotivLang := .allSubLeft shgMotivNNFNeg (.all 0 _) 0 _ a rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side
  · refine castAnt ?_ existential
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_motiv_set

end ShgMotivProof

/-- Example 7.6.1: the original normal-form proof of B ->. Below the
exact displayed midsequent are forall-subformula-left at z, exists-subformula-left
with eigenvariable y, and forall-subformula-left at x with term a. -/
@[blueprint "chap7__example_7_6_1" (main := true)]
def shgMotivOriginalProof [DecidableEq (FormulaN shgMotivLang)] :
    G2nnfProofTree (by rfl : shgMotivLang.withoutEquality)
      (LCS.Finset.ofList [shgMotivNNFNeg]) ∅ :=
  ShgMotivProof.originalTree

/-- The original displayed B is exactly the NNF of not A and satisfies
the sentence/rectification boundary needed by the later SHG theorem. -/
@[blueprint "chap7__example_7_6_1" (main := true)]
theorem shgMotivPreparation :
    (FormulaN.neg shgMotivExFormula).toNNF = shgMotivNNFNeg ∧
    shgMotivNNFNeg.isNNF ∧
    LCS.FirstOrder.Semantics.Subformulae.isRectified shgMotivNNFNeg ∧
    FormulaN.isClosed shgMotivNNFNeg 

/-- Example 7.6.1: the new ground midsequent after y is replaced by f(a). -/
@[blueprint "chap7__example_7_6_1"]
def shgMotivTransformedMidsequent : FormulaN shgMotivLang :=
  .conj
    (.disj ShgMotivProof.p
      (ShgMotivProof.r (.func .f (shgMotivVec1 ShgMotivProof.a))))
    (.conj (.neg (ShgMotivProof.r (.func .f (shgMotivVec1 ShgMotivProof.a))))
      (.neg ShgMotivProof.p))

namespace ShgMotivTransformedProof
set_option backward.isDefEq.respectTransparency false
open LCS.FirstOrder.SemanticsN LCS.FirstOrder.Semantics.Subformulae

abbrev F := FormulaN shgMotivLang

abbrev a : Term shgMotivLang := .const ShgMotivConst.a

abbrev p : F := .predN .P (shgMotivVec1 a)

abbrev r (t : Term shgMotivLang) : F := .predN .R (shgMotivVec2 a t)

@[blueprint "chap7__example_7_6_1"]
abbrev fa : Term shgMotivLang := .func .f (shgMotivVec1 a)

abbrev q : F := r fa

abbrev u : F := .all 2 (.neg (r (.var 2)))

abbrev afterAll : F := .conj (.disj p q) (.conj u (.neg p))

variable [DecidableEq F]

abbrev Tree (Γ : LCS.Finset F) :=
  G2nnfProofTree (by rfl : shgMotivLang.withoutEquality) Γ ∅

def castAnt {Γ Γ' : LCS.Finset F} (h : Γ = Γ') (t : Tree Γ) : Tree Γ' :=
  h ▸ t

open ShgMotivProof (substVec1 substVec2)

macro "shg_transformed_set" : tactic => `(tactic|
  ((try simp only [List.getElem_cons_zero, List.getElem_cons_succ, Prod.fst, Prod.snd]) <;>
   (apply LCS.Finset.ext; intro F
    simp [LCS.Finset.mem_insert, LCS.Finset.mem_ofList,
      LCS.Finset.mem_singleton, List.getElem_cons_zero, List.getElem_cons_succ,
      shgMotivTransformedMidsequent, shgMotivSkolemized, afterAll, p, q, r, u, a, fa,
      ShgMotivProof.p, ShgMotivProof.r, ShgMotivProof.a,
      shgMotivLang, formulaSubstN, substVec1, substVec2, termSubst,
      MaxQuantifierOccurrence.replace, or_assoc, or_left_comm, or_comm])))

macro "shg_transformed_side" : tactic => `(tactic|
  (refine ⟨?_, ?_, ?_, ?_⟩ <;>
   simp [G2nnfRuleCore.LogicalSideConditions, G2nnfRuleCore.conclusion,
     G2nnfRuleCore.premises, AllNNF, AllRectified,
     LCS.Finset.mem_insert, LCS.Finset.mem_ofList, LCS.Finset.mem_singleton,
     FormulaN.isNNF, isRectified, boundVarsFresh, distinctQuantifierBindings,
     formulaFVN, formulaBVN, termFV, isFreeForN, formulaSubstN, termSubst,
     MaxQuantifierOccurrence.replace, shgMotivTransformedMidsequent, shgMotivSkolemized,
     afterAll, p, q, r, u, a, fa,
     ShgMotivProof.p, ShgMotivProof.r, ShgMotivProof.a, shgMotivVec1, shgMotivVec2,
     Set.iUnion, Set.union, Set.inter, Set.diff, Set.singleton, Set.empty,
     Fin.exists_fin_succ, Fin.forall_fin_succ] <;>
   simp [Membership.mem, Set.iUnion, Set.union, Set.diff, Set.singleton, Set.empty,
     shgMotivLang, termFV, shgMotivVec1, shgMotivVec2,
     Fin.exists_fin_succ, Fin.forall_fin_succ] <;> (intros; omega)))

def pAx : Tree (LCS.Finset.ofList [p, .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .axiomCompLeft p rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.axiom_ rule ⟨rfl, rfl⟩ rfl ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side

def rAx : Tree (LCS.Finset.ofList [q, .neg q]) := by
  let rule : G2nnfRuleCore shgMotivLang := .axiomCompLeft q rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.axiom_ rule ⟨rfl, rfl⟩ rfl ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side

def pWeak : Tree (LCS.Finset.ofList [p, .neg q, .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .weakLeft (.neg q) (LCS.Finset.ofList [p, .neg p]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side
  · refine castAnt ?_ pAx
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_transformed_set

def rWeak : Tree (LCS.Finset.ofList [q, .neg q, .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .weakLeft (.neg p) (LCS.Finset.ofList [q, .neg q]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side
  · refine castAnt ?_ rAx
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_transformed_set

def disjunction : Tree (LCS.Finset.ofList [.disj p q, .neg q, .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .disjLeft p q (LCS.Finset.ofList [.neg q, .neg p]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.twoPremise rule trivial rfl ?_ ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side
  · refine castAnt ?_ pWeak
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_transformed_set
  · refine castAnt ?_ rWeak
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_transformed_set

def innerConj1 : Tree (LCS.Finset.ofList [.disj p q, .conj (.neg q) (.neg p), .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .conjLeft1 (.neg q) (.neg p) (LCS.Finset.ofList [.disj p q, .neg p]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side
  · refine castAnt ?_ disjunction
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_transformed_set

def innerConj2 : Tree (LCS.Finset.ofList [.disj p q, .conj (.neg q) (.neg p)]) := by
  let rule : G2nnfRuleCore shgMotivLang := .conjLeft2 (.neg q) (.neg p) (LCS.Finset.ofList [.disj p q, .conj (.neg q) (.neg p)]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side
  · refine castAnt ?_ innerConj1
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_transformed_set

def outerConj1 : Tree (LCS.Finset.ofList [shgMotivTransformedMidsequent, .conj (.neg q) (.neg p)]) := by
  let rule : G2nnfRuleCore shgMotivLang := .conjLeft1 (.disj p q) (.conj (.neg q) (.neg p)) (LCS.Finset.ofList [.conj (.neg q) (.neg p)]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side
  · refine castAnt ?_ innerConj2
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_transformed_set

def midTree : Tree (LCS.Finset.ofList [shgMotivTransformedMidsequent]) := by
  let rule : G2nnfRuleCore shgMotivLang := .conjLeft2 (.disj p q) (.conj (.neg q) (.neg p)) (LCS.Finset.ofList [shgMotivTransformedMidsequent]) ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side
  · refine castAnt ?_ outerConj1
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_transformed_set

def universalInner : Tree (LCS.Finset.ofList [afterAll]) := by
  let rule : G2nnfRuleCore shgMotivLang := .allSubLeft afterAll (.conjRight (.disj p q) (.conjLeft (.all 2 (.neg (r (.var 2)))) (.neg p))) 2 (.neg (r (.var 2))) fa rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side
  · refine castAnt ?_ midTree
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_transformed_set

def transformedTree : Tree (LCS.Finset.ofList [shgMotivSkolemized]) := by
  let rule : G2nnfRuleCore shgMotivLang := .allSubLeft shgMotivSkolemized (.all 0 _) 0 _ a rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.onePremise rule trivial rfl ?_ ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side
  · refine castAnt ?_ universalInner
    dsimp only [rule, G2nnfRuleCore.premises]
    shg_transformed_set

end ShgMotivTransformedProof

/-- Example 7.6.1: the transformed proof with the existential inference
removed, retaining the two universal inferences below the new midsequent. -/
@[blueprint "chap7__example_7_6_1" (main := true)]
def shgMotivTransformedProof [DecidableEq (FormulaN shgMotivLang)] :
    G2nnfProofTree (by rfl : shgMotivLang.withoutEquality)
      (LCS.Finset.ofList [shgMotivSkolemized]) ∅ :=
  ShgMotivTransformedProof.transformedTree

set_option backward.isDefEq.respectTransparency false in
/-- The new midsequent is the displayed substitution instance y ↦ f(a). -/
@[blueprint "chap7__example_7_6_1"]
theorem shgMotivMidsequent_substitution :
    formulaSubstN shgMotivMidsequent ShgMotivTransformedProof.fa 1 =
      shgMotivTransformedMidsequent 

end LCS.Herbrand.SHGTheorem
end
