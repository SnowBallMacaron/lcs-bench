import LCS.Item
import LCS.Util
import LCS.Herbrand.NNFHauptsatz
import LCS.Herbrand.HerbrandTheorem
import Attach
import LCS.Herbrand.SHGTheorem.CompoundInstances.ProofsStamp

section
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.Herbrand.NNFHauptsatz
open LCS.Herbrand.HerbrandTheorem

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

namespace CInstance

/-- Definition 7.6.3: Extract the formula of a compound instance.
Literal and binary-connective nodes preserve their constructors. A universal
node with children `h₀, h₁, ..., hₖ` produces the right-nested conjunction
`H₀ ∧ (H₁ ∧ ... ∧ Hₖ)` in that order. A sole child produces `H₀`.
The constructor supplies `h₀` structurally, enforcing nonemptiness. -/
@[blueprint "chap7__definition_7_6_3"]
def toFormula {L : Language} : CInstance L → FormulaN L
  | .atom B _ => B
  | .negAtom B _ => .neg B
  | .connective true _ _ H K => .conj (toFormula H) (toFormula K)
  | .connective false _ _ H K => .disj (toFormula H) (toFormula K)
  | .forallInst _ _ _ h₀ _ hsRest _ _ =>
    -- Each suffix receives its first child, so no terminal formula is added.
    (hsRest.map toFormula).foldr
      (fun f rest first => .conj first (rest f)) id (toFormula h₀)

-- ===================================================================
-- Definition 7.6.3 (companion def): CInstance.closedTerms
-- ===================================================================

/-- Definition 7.6.3 (companion def): Reconstructs the source Skolem form formula from which a CInstance derivation tree was built. - atom B _ => B (the atomic formula) - negAtom B _ => neg B (the negated atomic formula) - connective true C D _ _ => conj C D (recorded by the constructor) - connective false C D _ _ => disj C D (recorded by the constructor) - forallInst x C ts hs => all x C (the universal quantifier) -/
@[blueprint "chap7__definition_7_6_3"]
def source {L : Language} : CInstance L → FormulaN L
  | .atom B _ => B
  | .negAtom B _ => .neg B
  | .connective true C D _ _ => .conj C D
  | .connective false C D _ _ => .disj C D
  | .forallInst x C _ _ _ _ _ _ => .all x C

end CInstance
end LCS.Herbrand.SHGTheorem
namespace LCS.Herbrand.SHGTheorem
open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN LCS.FirstOrder.SyntaxN.Substitution

-- ATTACH-BLOCKER: mutual
mutual
/-- Definition 7.6.3 (companion def): A CInstance derivation tree is WellFormed when every node's children have sources matching the textbook's Def 7.6.3 conditions: - `connective star C D H K`: sources of H and K match the parent's operands (Def 7.6.3(ii) requirement that H is a c-instance *of C* and K is a c-instance *of D*), and both children are recursively WellFormed. - `forallInst x C t₀ h₀ tsRest hsRest`: lengths `tsRest.length = hsRest.length` match, `h₀.source = C[t₀/x]` and each `hsRest[i]` has source `C[tsRest[i]/x]`, and every child is recursively WellFormed. (Non-emptiness k ≥ 1 is enforced structurally by the constructor splitting out `t₀, h₀`.) For atom and negAtom nodes, WellFormed holds trivially (no children). -/
@[blueprint "chap7__definition_7_6_3"]
def CInstance.WellFormed {L : Language} : CInstance L → Prop
  | .atom _ _ => True
  | .negAtom _ _ => True
  | .connective _ C D H K =>
    CInstance.source H = C ∧ CInstance.source K = D ∧
    CInstance.WellFormed H ∧ CInstance.WellFormed K
  | .forallInst x C t₀ h₀ tsRest hsRest _ _ =>
    h₀.source = formulaSubstN C t₀ x ∧
    CInstance.WellFormed h₀ ∧
    CInstance.WellFormedList x C tsRest hsRest

/-- Definition 7.6.3 (companion def): Auxiliary for WellFormed that
walks the parallel lists of terms and c-instance children, checking
each child's source matches the substitution instance. -/
@[blueprint "chap7__definition_7_6_3"]
def CInstance.WellFormedList {L : Language} (x : Nat) (C : FormulaN L)
    : List (Term L) → List (CInstance L) → Prop
  | [], [] => True
  | t :: ts, h :: hs =>
    h.source = formulaSubstN C t x ∧ CInstance.WellFormed h ∧
    CInstance.WellFormedList x C ts hs
  | _, _ => False
end

-- ===================================================================
-- Definition 7.6.3 (companion def): isCInstanceOf
-- ===================================================================

/-- Definition 7.6.3 (companion def): Predicate that a formula H is a c-instance of the Skolem form B: there exists a CInstance derivation `ci` derived from B such that `ci.toFormula = H` and the derivation is WellFormed. The `CInstance.source` function reconstructs the source formula from the derivation tree, ensuring the derivation actually corresponds to B. The WellFormed condition ensures that `forallInst` children have sources matching the substitution instances of their parent's body. Textbook Def 7.6.3 opens with "Let A be a rectified sentence and let B be its Skolem form" — this is an EXTERNAL framing assumption on theorems that USE `isCInstanceOf` (e.g. Lem 7.6.1 `cInstance_combination`, `herbrand_half_lemma`), NOT an internal conjunct of the membership predicate. Clause (i) of the textbook ("atomic B is its own c-instance") holds WITHOUT any rectified/closed hypothesis on B, so bundling `isSkolemNormalForm B` inside would be strictly stronger than the textbook relation. -/
@[blueprint "chap7__definition_7_6_3" (main := true)]
def isCInstanceOf {L : Language}
    (H : FormulaN L) (B : FormulaN L) : Prop :=
  ∃ (ci : CInstance L), ci.source = B ∧ ci.toFormula = H ∧
    CInstance.WellFormed ci

-- ===================================================================
-- Definition 7.6.3 (theorem): CInstance.isQuantifierFree
-- ===================================================================

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Helper: an atomic formula is quantifier-free. -/
theorem isAtomic_isQuantifierFree {L : Language}
    (B : FormulaN L) (h : B.isAtomic) :
    LCS.FirstOrder.SemanticsN.isQuantifierFree B := by
-- BEGIN PROOF
  cases B <;> simp_all [FormulaN.isAtomic,
    LCS.FirstOrder.SemanticsN.isQuantifierFree]

end LCS.Herbrand.SHGTheorem
end
