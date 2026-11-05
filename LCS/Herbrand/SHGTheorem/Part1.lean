import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.HerbrandTheorem
import Attach
import LCS.Herbrand.SHGTheorem.Part1.ProofsStamp

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
-- Definition 7.6.3: CInstance — Compound instance derivation tree
-- ===================================================================

/-- Definition 7.6.3: Let A be a rectified sentence and let B be its Skolem form. The set of compound instances (c-instances) of B is defined inductively: (i) If B is an atomic formula C, then B is its only c-instance; if B is the negation not C of an atomic formula, then B is its only c-instance. (ii) If B = (C * D) where * is or or and, for any c-instance H of C and c-instance K of D, (H * K) is a c-instance of B. (iii) If B = forall x C, for any k closed terms t_1,...,t_k, if H_i is a c-instance of C[t_i/x] for i = 1,...,k, then H_1 and ... and H_k is a c-instance of B. CInstance is an inductive derivation tree witnessing that a quantifier-free formula is a c-instance of a Skolem form B. The Bool parameter in connective distinguishes conjunction (true) from disjunction (false). -/
@[blueprint "chap7__definition_7_6_3"]
inductive CInstance (L : Language) : Type where
  /-- c-instance atomic case (i): an atomic formula B is its own
      c-instance. Requires proof that B is atomic. -/
  | atom (B : FormulaN L) (hAtom : B.isAtomic) : CInstance L
  /-- c-instance negated atomic case (i): the negation not B of an
      atomic formula B is its own c-instance. Requires proof that B
      is atomic. -/
  | negAtom (B : FormulaN L) (hAtom : B.isAtomic) : CInstance L
  /-- c-instance connective case (ii): if H is a c-instance of C and
      K is a c-instance of D, then (H * K) is a c-instance of (C * D).
      star = true means conjunction (and), star = false means
      disjunction (or). The parent operands `C, D` are recorded
      explicitly; callers must tie them to child sources via
      `CInstance.WellFormed` (which enforces `source H = C ∧ source K = D`)
      or via the indexed-source invariant `CInstance.source = …`. -/
  | connective (star : Bool) (C D : FormulaN L)
      (H K : CInstance L) : CInstance L
  /-- c-instance universal quantifier case (iii): if B = forall x C,
      for closed terms t_1,...,t_k (k ≥ 1), if H_i is a c-instance of
      C[t_i/x], then H_1 and ... and H_k is a c-instance of B.

      STRUCTURAL encoding of k ≥ 1: the first term `t₀` and first
      child `h₀` are split out as explicit fields, and `tsRest` /
      `hsRest` hold the remaining k-1 pairs. This enforces Def
      7.6.3(iii)'s non-emptiness requirement at the type level so
      `toFormula` never hits an empty-list sentinel, and the nested
      `List (CInstance L)` field only carries the TAIL so there is no
      ambiguity about the minimum instantiation count.

      Closed-term obligation (Def 5.2.4): `hGround₀` covers `t₀`;
      `hGroundRest` covers every element of `tsRest`. Length-match
      (`tsRest.length = hsRest.length`) is enforced by `CInstance.WellFormed`
      — we cannot put it in the constructor because `hsRest.length`
      triggers nested-inductive restrictions. -/
  | forallInst (x : Nat) (C : FormulaN L)
      (t₀ : Term L) (h₀ : CInstance L)
      (tsRest : List (Term L)) (hsRest : List (CInstance L))
      (hGround₀ : LCS.FirstOrder.Basic.Term.isClosed t₀)
      (hGroundRest : ∀ t ∈ tsRest, LCS.FirstOrder.Basic.Term.isClosed t) :
      CInstance L

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

end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem
namespace ShgMotivProof
-- ATTACH-BLOCKER: global set_option
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
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev q : F := r (.var 1)
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev u : F := .all 2 (.neg (r (.var 2)))
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev e : F := .ex 1 (r (.var 1))
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev afterAll : F := .conj (.disj p q) (.conj u (.neg p))
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev afterEx : F := .conj (.disj p e) (.conj u (.neg p))

end ShgMotivProof
end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem
namespace ShgMotivProof
-- ATTACH-BLOCKER: global set_option
set_option backward.isDefEq.respectTransparency false
open LCS.FirstOrder.SemanticsN LCS.FirstOrder.Semantics.Subformulae
-- ATTACH-BLOCKER: variable
variable [DecidableEq F]

-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev Tree (Γ : LCS.Finset F) :=
  G2nnfProofTree (by rfl : shgMotivLang.withoutEquality) Γ ∅

-- ATTACH-BLOCKER: section variables: helper requires front context
def castAnt {Γ Γ' : LCS.Finset F} (h : Γ = Γ') (t : Tree Γ) : Tree Γ' :=
  h ▸ t

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem substVec1 (u t : Term shgMotivLang) (x : Nat) :
    (fun i => termSubst (shgMotivVec1 u i) t x) =
      shgMotivVec1 (termSubst u t x) := by
  funext i
  rcases i with ⟨i, hi⟩
  have h : i = 0 := by omega
  subst i
  rfl

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem substVec2 (u v t : Term shgMotivLang) (x : Nat) :
    (fun i => termSubst (shgMotivVec2 u v i) t x) =
      shgMotivVec2 (termSubst u t x) (termSubst v t x) := by
  funext i
  rcases i with ⟨i, hi⟩
  by_cases h : i = 0
  · subst i; rfl
  · have h : i = 1 := by omega
    subst i; rfl

-- ATTACH-BLOCKER: unsupported untagged macro
macro "shg_motiv_set" : tactic => `(tactic|
  ((try simp only [List.getElem_cons_zero, List.getElem_cons_succ, Prod.fst, Prod.snd]) <;>
   (apply LCS.Finset.ext; intro F
    simp [LCS.Finset.mem_insert, LCS.Finset.mem_ofList,
      LCS.Finset.mem_singleton, List.getElem_cons_zero, List.getElem_cons_succ,
      shgMotivMidsequent, shgMotivNNFNeg, afterAll, afterEx, p, q, r, u, e, a,
      shgMotivLang, formulaSubstN, substVec1, substVec2, termSubst,
      MaxQuantifierOccurrence.replace, or_assoc, or_left_comm, or_comm])))

-- ATTACH-BLOCKER: unsupported untagged macro
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

-- ATTACH-BLOCKER: section variables: helper requires front context
def pAx : Tree (LCS.Finset.ofList [p, .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .axiomCompLeft p rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.axiom_ rule ⟨rfl, rfl⟩ rfl ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side

-- ATTACH-BLOCKER: section variables: helper requires front context
def rAx : Tree (LCS.Finset.ofList [q, .neg q]) := by
  let rule : G2nnfRuleCore shgMotivLang := .axiomCompLeft q rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.axiom_ rule ⟨rfl, rfl⟩ rfl ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_motiv_set
  · dsimp [rule]
    shg_motiv_side

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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
end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem
namespace ShgMotivProof
-- ATTACH-BLOCKER: variable
variable [DecidableEq F]

-- ATTACH-BLOCKER: section variables: helper requires front context
def nodeCount {Γ Δ : LCS.Finset F} :
    G2nnfProofTree (by rfl : shgMotivLang.withoutEquality) Γ Δ → Nat
  | .leaf _ _ h _ _ => h.elim
  | .extraAxiom _ _ h _ _ => h.elim
  | .axiom_ _ _ _ _ => 1
  | .onePremise _ _ _ _ sub => nodeCount sub + 1
  | .twoPremise _ _ _ _ left right => nodeCount left + nodeCount right + 1

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem nodeCount_castAnt {Γ Γ' : LCS.Finset F}
    (h : Γ = Γ') (t : Tree Γ) : nodeCount (castAnt h t) = nodeCount t := by
  cases h
  rfl

end ShgMotivProof
end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem

/-- Example 7.6.1: the displayed original midsequent has an explicit
propositional proof. Both complementary leaves are bare; the two weakenings
and both pairs of conjunction-left rules are actual nodes. -/
@[blueprint "chap7__example_7_6_1"]
def shgMotivOriginalMidProof [DecidableEq (FormulaN shgMotivLang)] :
    G2nnfProofTree (by rfl : shgMotivLang.withoutEquality)
      (LCS.Finset.ofList [shgMotivMidsequent]) ∅ :=
  ShgMotivProof.midTree

/-- Example 7.6.1: the original normal-form proof of B ->. Below the
exact displayed midsequent are forall-subformula-left at z, exists-subformula-left
with eigenvariable y, and forall-subformula-left at x with term a. -/
@[blueprint "chap7__example_7_6_1" (main := true)]
def shgMotivOriginalProof [DecidableEq (FormulaN shgMotivLang)] :
    G2nnfProofTree (by rfl : shgMotivLang.withoutEquality)
      (LCS.Finset.ofList [shgMotivNNFNeg]) ∅ :=
  ShgMotivProof.originalTree

-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option backward.isDefEq.respectTransparency false in
/-- The expanded proof has twelve primitive rule nodes; nine form the
propositional proof above and including the displayed original midsequent. -/
theorem shgMotivOriginalProof_expanded [DecidableEq (FormulaN shgMotivLang)] :
    ShgMotivProof.nodeCount shgMotivOriginalProof = 12 ∧
    ShgMotivProof.nodeCount shgMotivOriginalMidProof = 9 := by
  simp [shgMotivOriginalProof, shgMotivOriginalMidProof,
    ShgMotivProof.originalTree, ShgMotivProof.existential,
    ShgMotivProof.universalInner, ShgMotivProof.midTree,
    ShgMotivProof.outerConj1, ShgMotivProof.innerConj2,
    ShgMotivProof.innerConj1, ShgMotivProof.disjunction,
    ShgMotivProof.pWeak, ShgMotivProof.rWeak,
    ShgMotivProof.pAx, ShgMotivProof.rAx,
    ShgMotivProof.nodeCount_castAnt, ShgMotivProof.nodeCount]

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

end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem
namespace ShgMotivTransformedProof
-- ATTACH-BLOCKER: global set_option
set_option backward.isDefEq.respectTransparency false
open LCS.FirstOrder.SemanticsN LCS.FirstOrder.Semantics.Subformulae

-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev F := FormulaN shgMotivLang
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev a : Term shgMotivLang := .const ShgMotivConst.a
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev p : F := .predN .P (shgMotivVec1 a)
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev r (t : Term shgMotivLang) : F := .predN .R (shgMotivVec2 a t)
@[blueprint "chap7__example_7_6_1"]
abbrev fa : Term shgMotivLang := .func .f (shgMotivVec1 a)
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev q : F := r fa
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev u : F := .all 2 (.neg (r (.var 2)))
-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev afterAll : F := .conj (.disj p q) (.conj u (.neg p))

end ShgMotivTransformedProof
end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem
namespace ShgMotivTransformedProof
-- ATTACH-BLOCKER: global set_option
set_option backward.isDefEq.respectTransparency false
open LCS.FirstOrder.SemanticsN LCS.FirstOrder.Semantics.Subformulae
-- ATTACH-BLOCKER: variable
variable [DecidableEq F]

-- ATTACH-BLOCKER: unsupported untagged abbrev
abbrev Tree (Γ : LCS.Finset F) :=
  G2nnfProofTree (by rfl : shgMotivLang.withoutEquality) Γ ∅

-- ATTACH-BLOCKER: section variables: helper requires front context
def castAnt {Γ Γ' : LCS.Finset F} (h : Γ = Γ') (t : Tree Γ) : Tree Γ' :=
  h ▸ t

end ShgMotivTransformedProof
end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem
namespace ShgMotivTransformedProof
-- ATTACH-BLOCKER: global set_option
set_option backward.isDefEq.respectTransparency false
open LCS.FirstOrder.SemanticsN LCS.FirstOrder.Semantics.Subformulae
-- ATTACH-BLOCKER: variable
variable [DecidableEq F]
open ShgMotivProof (substVec1 substVec2)

-- ATTACH-BLOCKER: unsupported untagged macro
macro "shg_transformed_set" : tactic => `(tactic|
  ((try simp only [List.getElem_cons_zero, List.getElem_cons_succ, Prod.fst, Prod.snd]) <;>
   (apply LCS.Finset.ext; intro F
    simp [LCS.Finset.mem_insert, LCS.Finset.mem_ofList,
      LCS.Finset.mem_singleton, List.getElem_cons_zero, List.getElem_cons_succ,
      shgMotivTransformedMidsequent, shgMotivSkolemized, afterAll, p, q, r, u, a, fa,
      ShgMotivProof.p, ShgMotivProof.r, ShgMotivProof.a,
      shgMotivLang, formulaSubstN, substVec1, substVec2, termSubst,
      MaxQuantifierOccurrence.replace, or_assoc, or_left_comm, or_comm])))

-- ATTACH-BLOCKER: unsupported untagged macro
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

-- ATTACH-BLOCKER: section variables: helper requires front context
def pAx : Tree (LCS.Finset.ofList [p, .neg p]) := by
  let rule : G2nnfRuleCore shgMotivLang := .axiomCompLeft p rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.axiom_ rule ⟨rfl, rfl⟩ rfl ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side

-- ATTACH-BLOCKER: section variables: helper requires front context
def rAx : Tree (LCS.Finset.ofList [q, .neg q]) := by
  let rule : G2nnfRuleCore shgMotivLang := .axiomCompLeft q rfl ∅ ∅
  refine castAnt (Γ := rule.conclusion.1) ?_ (G2nnfDeductionTreeCore.axiom_ rule ⟨rfl, rfl⟩ rfl ?_)
  · dsimp [rule, G2nnfRuleCore.conclusion]
    shg_transformed_set
  · dsimp [rule]
    shg_transformed_side

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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

-- ATTACH-BLOCKER: section variables: helper requires front context
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
end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem

/-- Example 7.6.1: the transformed proof with the existential inference
removed, retaining the two universal inferences below the new midsequent. -/
@[blueprint "chap7__example_7_6_1" (main := true)]
def shgMotivTransformedProof [DecidableEq (FormulaN shgMotivLang)] :
    G2nnfProofTree (by rfl : shgMotivLang.withoutEquality)
      (LCS.Finset.ofList [shgMotivSkolemized]) ∅ :=
  ShgMotivTransformedProof.transformedTree

/-- Example 7.6.1: the actual propositional subtree at the new midsequent. -/
@[blueprint "chap7__example_7_6_1"]
def shgMotivTransformedMidProof [DecidableEq (FormulaN shgMotivLang)] :
    G2nnfProofTree (by rfl : shgMotivLang.withoutEquality)
      (LCS.Finset.ofList [shgMotivTransformedMidsequent]) ∅ :=
  ShgMotivTransformedProof.midTree

end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem
namespace ShgMotivProof
-- ATTACH-BLOCKER: variable
variable [DecidableEq F]

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Preorder rule and sequent trace of the concrete derivation. -/
def trace {Γ Δ : LCS.Finset F} :
    G2nnfProofTree (by rfl : shgMotivLang.withoutEquality) Γ Δ →
      List (G2nnfRuleCore shgMotivLang × LCS.Finset F × LCS.Finset F)
  | .leaf _ _ h _ _ => h.elim
  | .extraAxiom _ _ h _ _ => h.elim
  | .axiom_ rule _ _ _ => [(rule, Γ, Δ)]
  | .onePremise rule _ _ _ sub => (rule, Γ, Δ) :: trace sub
  | .twoPremise rule _ _ _ left right => (rule, Γ, Δ) :: (trace left ++ trace right)

-- ATTACH-BLOCKER: section variables: helper requires front context
def ruleCode : G2nnfRuleCore shgMotivLang → Nat
  | .allSubLeft .. => 0
  | .exSubLeft .. => 1
  | .axiomCompLeft .. => 2
  | .weakLeft .. => 3
  | .conjLeft1 .. => 4
  | .conjLeft2 .. => 5
  | .disjLeft .. => 6
  | _ => 7

-- ATTACH-BLOCKER: section variables: helper requires front context
def displayTrace {Γ Δ : LCS.Finset F}
    (t : G2nnfProofTree (by rfl : shgMotivLang.withoutEquality) Γ Δ) :=
  (trace t).map fun (rule, ant, suc) => (ruleCode rule, ant, suc)

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem trace_castAnt {Γ Γ' : LCS.Finset F}
    (h : Γ = Γ') (t : Tree Γ) : trace (castAnt h t) = trace t := by
  cases h; rfl

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem transformed_trace_castAnt {Γ Γ' : LCS.Finset F}
    (h : Γ = Γ') (t : Tree Γ) :
    trace (ShgMotivTransformedProof.castAnt h t) = trace t := by
  cases h; rfl

-- ATTACH-BLOCKER: section variables: helper requires front context
theorem image_ofList (f : F → F) (xs : List F) :
    LCS.Finset.image f (LCS.Finset.ofList xs) = LCS.Finset.ofList (xs.map f) := by
  apply LCS.Finset.ext
  intro B
  simp [LCS.Finset.mem_image, LCS.Finset.mem_ofList]

end ShgMotivProof
end LCS.Herbrand.SHGTheorem
end

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem

set_option backward.isDefEq.respectTransparency false in
/-- The new midsequent is the displayed substitution instance y ↦ f(a). -/
@[blueprint "chap7__example_7_6_1"]
theorem shgMotivMidsequent_substitution :
    formulaSubstN shgMotivMidsequent ShgMotivTransformedProof.fa 1 =
      shgMotivTransformedMidsequent 



-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option backward.isDefEq.respectTransparency false in
/-- The displayed proof surgery, checked on the actual preorder traces.
The original outer-universal conclusion is replaced by the Skolemized one;
the next (existential) inference is deleted. All remaining rule kinds and
both sides of every remaining sequent are preserved under y ↦ f(a). -/
theorem shgMotivSubstitutionDeletion [DecidableEq (FormulaN shgMotivLang)] :
    ShgMotivProof.displayTrace shgMotivTransformedProof =
      (0, LCS.Finset.ofList [shgMotivSkolemized], (∅ : LCS.Finset (FormulaN shgMotivLang))) ::
        ((ShgMotivProof.displayTrace shgMotivOriginalProof).drop 2).map
          (fun (rule, ant, suc) =>
            (rule, LCS.Finset.image
              (fun A => formulaSubstN A ShgMotivTransformedProof.fa 1) ant,
              LCS.Finset.image
              (fun A => formulaSubstN A ShgMotivTransformedProof.fa 1) suc)) := by
  have hi (f : FormulaN shgMotivLang → FormulaN shgMotivLang) :
      LCS.Finset.image f (∅ : LCS.Finset (FormulaN shgMotivLang)) = (∅ : LCS.Finset (FormulaN shgMotivLang)) := by
    apply LCS.Finset.ext
    intro B
    simp [LCS.Finset.mem_image]
  have hii (f : FormulaN shgMotivLang → FormulaN shgMotivLang)
      (A : FormulaN shgMotivLang) (Γ : LCS.Finset (FormulaN shgMotivLang)) :
      LCS.Finset.image f (LCS.Finset.insert A Γ) =
        LCS.Finset.insert (f A) (LCS.Finset.image f Γ) := by
    apply LCS.Finset.ext
    intro B
    simp [LCS.Finset.mem_image, LCS.Finset.mem_insert, exists_or, eq_comm]
  simp only [shgMotivTransformedProof, shgMotivOriginalProof,
    ShgMotivProof.displayTrace,
    ShgMotivProof.originalTree, ShgMotivProof.existential, ShgMotivProof.universalInner, ShgMotivProof.midTree, ShgMotivProof.outerConj1, ShgMotivProof.innerConj2, ShgMotivProof.innerConj1, ShgMotivProof.disjunction, ShgMotivProof.pWeak, ShgMotivProof.rWeak, ShgMotivProof.pAx, ShgMotivProof.rAx,
    ShgMotivTransformedProof.transformedTree, ShgMotivTransformedProof.universalInner, ShgMotivTransformedProof.midTree, ShgMotivTransformedProof.outerConj1, ShgMotivTransformedProof.innerConj2, ShgMotivTransformedProof.innerConj1, ShgMotivTransformedProof.disjunction, ShgMotivTransformedProof.pWeak, ShgMotivTransformedProof.rWeak, ShgMotivTransformedProof.pAx, ShgMotivTransformedProof.rAx,
    ShgMotivProof.trace_castAnt, ShgMotivProof.transformed_trace_castAnt,
    ShgMotivProof.trace, ShgMotivProof.ruleCode, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero,
    Prod.fst, Prod.snd, G2nnfRuleCore.conclusion,
    ShgMotivProof.image_ofList, hi, hii]
  simp [shgMotivMidsequent, shgMotivTransformedMidsequent,
    ShgMotivProof.afterAll, ShgMotivTransformedProof.afterAll,
    ShgMotivProof.p, ShgMotivProof.q, ShgMotivProof.r, ShgMotivProof.u,
    ShgMotivProof.a, ShgMotivTransformedProof.p, ShgMotivTransformedProof.q,
    ShgMotivTransformedProof.r, ShgMotivTransformedProof.u,
    ShgMotivTransformedProof.a, ShgMotivTransformedProof.fa, shgMotivLang,
    formulaSubstN, ShgMotivProof.substVec1, ShgMotivProof.substVec2, termSubst]
  repeat first
    | apply And.intro
    | (apply LCS.Finset.ext; intro B
       simp [LCS.Finset.mem_insert, LCS.Finset.mem_ofList,
         or_assoc, or_left_comm, or_comm])


-- ATTACH-BLOCKER: scoped helper requires manual relocation
set_option backward.isDefEq.respectTransparency false in
/-- The new proof has eleven primitive nodes, with the nine-node ground
propositional subtree at its displayed midsequent. -/
theorem shgMotivTransformedProof_expanded [DecidableEq (FormulaN shgMotivLang)] :
    ShgMotivProof.nodeCount shgMotivTransformedProof = 11 ∧
    ShgMotivProof.nodeCount shgMotivTransformedMidProof = 9 := by
  have hc {Γ Γ' : LCS.Finset ShgMotivProof.F} (h : Γ = Γ')
      (t : ShgMotivProof.Tree Γ) :
      ShgMotivProof.nodeCount (ShgMotivTransformedProof.castAnt h t) =
        ShgMotivProof.nodeCount t := by
    cases h; rfl
  simp [shgMotivTransformedProof, shgMotivTransformedMidProof,
    ShgMotivTransformedProof.transformedTree, ShgMotivTransformedProof.universalInner, ShgMotivTransformedProof.midTree, ShgMotivTransformedProof.outerConj1, ShgMotivTransformedProof.innerConj2, ShgMotivTransformedProof.innerConj1, ShgMotivTransformedProof.disjunction, ShgMotivTransformedProof.pWeak, ShgMotivTransformedProof.rWeak, ShgMotivTransformedProof.pAx, ShgMotivTransformedProof.rAx,
    hc, ShgMotivProof.nodeCount]

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
-- Definition 7.6.2 (companion def): existentialDescriptors
-- ===================================================================

/-- Definition 7.6.2 (companion def): The existential occurrences of
`A`, paired with their exact ordered universal scopes, starting in
the supplied outer `scope`. This generalized form is used to prove
that the Skolem traversal and the descriptor traversal split at the
same connective boundaries. -/
@[blueprint "chap7__definition_7_6_2"]
def existentialDescriptorsAux {L : Language}
    (A : FormulaN L) (scope : List Nat) :
    List (FormulaN L × List Nat) :=
  (universalScopeAux A scope).filterMap fun pair =>
    match pair.1 with
    | .ex _ _ => some pair
    | _ => none

/-- Definition 7.6.2 (companion def): The existential occurrences of
`A`, paired with their exact ordered universal scopes. This is the
preorder list computed by `universalScopeAux A []`, filtered only by
constructor shape. `List.filterMap` deliberately preserves both order
and multiplicity: list position, rather than structural formula
equality, is the identity of an existential occurrence. -/
@[blueprint "chap7__definition_7_6_2"]
def existentialDescriptors {L : Language}
    (A : FormulaN L) : List (FormulaN L × List Nat) :=
  existentialDescriptorsAux A []

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction, LCS.Herbrand.SHGTheorem.Herbrand.SkolemBounds, LCS.Herbrand.SHGTheorem.Main.GroundMatrix, LCS.Herbrand.SHGTheorem.Main.SHG, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability, LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase, LCS.Herbrand.SHGTheorem.Part2, LCS.Herbrand.SHGTheorem.Part3, LCS.SLD.FirstOrder.GroundSemantics
/-- Definition 7.6.2 (helper): Number of descriptor cells generated
by the universal-scope traversal. Negations and implications are
leaves in `universalScopeAux`; on the NNF sources accepted by
`SkolemSpec`, those are precisely negated atoms and no implications. -/
def skolemDescriptorCount {L : Language} : FormulaN L → Nat
  | .predN _ _ => 0
  | .eq_ _ _ _ => 0
  | .neg _ => 0
  | .conj A B => skolemDescriptorCount A + skolemDescriptorCount B
  | .disj A B => skolemDescriptorCount A + skolemDescriptorCount B
  | .impl _ _ => 0
  | .all _ B => skolemDescriptorCount B
  | .ex _ B => 1 + skolemDescriptorCount B

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction, LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability, LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase, LCS.Herbrand.SHGTheorem.Part2
/-- Definition 7.6.2 (helper): Ordered scopes generated by the same
traversal as `existentialDescriptorsAux`, with formula payloads
erased. -/
def existentialScopesAux {L : Language} :
    FormulaN L → List Nat → List (List Nat)
  | .predN _ _, _ => []
  | .eq_ _ _ _, _ => []
  | .neg _, _ => []
  | .conj A B, scope =>
    existentialScopesAux A scope ++ existentialScopesAux B scope
  | .disj A B, scope =>
    existentialScopesAux A scope ++ existentialScopesAux B scope
  | .impl _ _, _ => []
  | .all x B, scope => existentialScopesAux B (scope ++ [x])
  | .ex _ B, scope => scope :: existentialScopesAux B scope

-- retained: used by LCS.Herbrand.SHGTheorem.Part2
/-- Descriptor traversal has exactly `skolemDescriptorCount A` cells. -/
theorem existentialDescriptorsAux_length {L : Language}
    (A : FormulaN L) (scope : List Nat) :
    (existentialDescriptorsAux A scope).length =
      skolemDescriptorCount A := by
  induction A generalizing scope with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj A B ihA ihB =>
    have hA := ihA scope
    have hB := ihB scope
    unfold existentialDescriptorsAux at hA hB
    simp [existentialDescriptorsAux, universalScopeAux,
      skolemDescriptorCount, hA, hB]
  | disj A B ihA ihB =>
    have hA := ihA scope
    have hB := ihB scope
    unfold existentialDescriptorsAux at hA hB
    simp [existentialDescriptorsAux, universalScopeAux,
      skolemDescriptorCount, hA, hB]
  | impl _ _ _ _ => rfl
  | all x B ih =>
    have hB := ih (scope ++ [x])
    unfold existentialDescriptorsAux at hB
    simp [existentialDescriptorsAux, universalScopeAux,
      skolemDescriptorCount, hB]
  | ex x B ih =>
    have hB := ih scope
    unfold existentialDescriptorsAux at hB
    simp [existentialDescriptorsAux, universalScopeAux,
      skolemDescriptorCount, hB, Nat.add_comm]

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.SyntaxAllocation, LCS.Herbrand.SHGTheorem.Part2
/-- Erasing formula payloads from the descriptor traversal yields the
exact ordered scope traversal. -/
theorem existentialDescriptorsAux_scopes {L : Language}
    (A : FormulaN L) (scope : List Nat) :
    (existentialDescriptorsAux A scope).map Prod.snd =
      existentialScopesAux A scope := by
  induction A generalizing scope with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ => rfl
  | conj A B ihA ihB =>
    have hA := ihA scope
    have hB := ihB scope
    unfold existentialDescriptorsAux at hA hB
    simp [existentialDescriptorsAux, universalScopeAux,
      existentialScopesAux, hA, hB]
  | disj A B ihA ihB =>
    have hA := ihA scope
    have hB := ihB scope
    unfold existentialDescriptorsAux at hA hB
    simp [existentialDescriptorsAux, universalScopeAux,
      existentialScopesAux, hA, hB]
  | impl _ _ _ _ => rfl
  | all x B ih =>
    have hB := ih (scope ++ [x])
    unfold existentialDescriptorsAux at hB
    simp [existentialDescriptorsAux, universalScopeAux,
      existentialScopesAux, hB]
  | ex x B ih =>
    have hB := ih scope
    unfold existentialDescriptorsAux at hB
    simp [existentialDescriptorsAux, universalScopeAux,
      existentialScopesAux, hB]

-- retained: used by LCS.Herbrand.SHGTheorem.Herbrand.LowerConstruction, LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability, LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase
/-- The ordered scope list has one cell per descriptor. -/
theorem existentialScopesAux_length {L : Language}
    (A : FormulaN L) (scope : List Nat) :
    (existentialScopesAux A scope).length =
      skolemDescriptorCount A := by
  rw [← existentialDescriptorsAux_scopes A scope, List.length_map,
    existentialDescriptorsAux_length]

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

end LCS.Herbrand.SHGTheorem
end

