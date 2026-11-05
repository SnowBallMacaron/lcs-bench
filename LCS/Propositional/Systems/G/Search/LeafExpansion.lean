import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import Attach
import LCS.Propositional.Systems.G.Search.LeafExpansion.ProofsStamp
attach_helper_namespace LCS.Propositional.Systems.G.Search.Proofs

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G

/-- The two stopping conventions of Definition 3.4.6. Systematic search
    closes axiom leaves immediately; atomic search expands them until all
    formulas are variables. -/
@[blueprint "chap3__definition_3_4_6"]
inductive SearchMode where
  | systematic
  | atomic
  deriving DecidableEq, Repr

end LCS.Propositional.Systems.G.Search
end

section
namespace LCS.Propositional.Systems.G.Search
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
variable {mode : SearchMode}

/-- Definition 3.4.6 (companion): A proposition is atomic if it is a
    propositional variable (PropFormulaNormalized.var _). -/
@[blueprint "chap3__definition_3_4_6"]
def isAtomicFormula : PropFormulaNormalized → Prop
  | .var _ => True
  | _ => False

/-- Definition 3.4.6 (companion): A proposition is nonatomic if it is not
    atomic, i.e. it has a top-level connective (neg, conj, disj, impl). -/
@[blueprint "chap3__definition_3_4_6"]
def isNonatomicFormula : PropFormulaNormalized → Prop
  | .var _ => False
  | _ => True

/-- Definition 3.4.6 (companion): Decidable version of isAtomicFormula
    for computation. -/
@[blueprint "chap3__definition_3_4_6"]
def isAtomicBool : PropFormulaNormalized → Bool
  | .var _ => true
  | _ => false

/-- Definition 3.4.6 (companion): Decidable version of isNonatomicFormula
    for computation. -/
@[blueprint "chap3__definition_3_4_6"]
def isNonatomicBool : PropFormulaNormalized → Bool
  | .var _ => false
  | _ => true

-- ========= Definition 3.4.6: Finished leaves and trees =========

/-- Definition 3.4.6 (companion): A leaf is finished when all formulas
    are atomic, or, in systematic mode, when it is an axiom. -/
@[blueprint "chap3__definition_3_4_6"]
def isFinishedLeaf (mode : SearchMode) (s : Sequent) : Prop :=
  (mode = .systematic ∧ isAxiom s) ∨
  (∀ A ∈ s.antecedent ++ s.succedent, isAtomicFormula A)

/-- Definition 3.4.6 (companion): Decidable version of isFinishedLeaf. -/
@[blueprint "chap3__definition_3_4_6"]
def isFinishedLeafBool (mode : SearchMode) (s : Sequent) : Bool :=
  ((mode == .systematic) &&
    (s.antecedent.any (fun A => s.succedent.any (fun B => A == B)))) ||
  ((s.antecedent ++ s.succedent).all isAtomicBool)

/-- Definition 3.4.6 (companion): All leaves of a deduction tree are
    finished. -/
@[blueprint "chap3__definition_3_4_6"]
def isFinishedTree (mode : SearchMode) {s : Sequent} (dt : DeductionTree s) : Prop :=
  ∀ s ∈ dt.leaves, isFinishedLeaf mode s

/-- Definition 3.4.6 (companion): Decidable version of isFinishedTree. -/
@[blueprint "chap3__definition_3_4_6"]
def isFinishedTreeBool (mode : SearchMode) {s : Sequent} (dt : DeductionTree s) : Bool :=
  dt.leaves.all (isFinishedLeafBool mode)

-- ========= Transport lemmas for indexed DeductionTree =========

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Transport through a type-index equality does not change the list of
    leaves. -/
theorem DeductionTree.leaves_eq_rec {s s' : Sequent} (heq : s' = s)
    (dt : DeductionTree s') : (heq ▸ dt : DeductionTree s).leaves = dt.leaves := by
-- BEGIN PROOF
  subst heq; rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Transport through a type-index equality does not change the conclusion
    (since the conclusion is the type index, it becomes the target index). -/
theorem DeductionTree.conclusion_eq_rec {s s' : Sequent} (heq : s' = s)
    (dt : DeductionTree s') :
    (heq ▸ dt : DeductionTree s).conclusion = s := by
-- BEGIN PROOF
  subst heq; rfl

-- ========= Definition 3.4.6: doSubstitution =========

/-- An address identifies one node, including unary edges, even when
    distinct nodes carry identical sequents. -/
@[blueprint "chap3__definition_3_4_6"]
inductive NodeAddress : {s : Sequent} → DeductionTree s → Sequent → Type where
  | here {s : Sequent} (tree : DeductionTree s) : NodeAddress tree s
  | down {p c t : Sequent} {rule : GentzenStep1 p c} {child : DeductionTree p} :
      NodeAddress child t → NodeAddress (.onePremise rule child) t
  | left {p q c t : Sequent} {rule : GentzenStep2 p q c}
      {left : DeductionTree p} {right : DeductionTree q} :
      NodeAddress left t → NodeAddress (.twoPremise rule left right) t
  | right {p q c t : Sequent} {rule : GentzenStep2 p q c}
      {left : DeductionTree p} {right : DeductionTree q} :
      NodeAddress right t → NodeAddress (.twoPremise rule left right) t

/-- Definition 3.4.6: Substitute at the single addressed node. -/
@[blueprint "chap3__definition_3_4_6"]
def doSubstitution {s target : Sequent} {tree : DeductionTree s}
    (address : NodeAddress tree target) (replacement : DeductionTree target) :
    DeductionTree s :=
  match address with
  | .here _ => replacement
  | .down (rule := rule) a => .onePremise rule (doSubstitution a replacement)
  | .left (rule := rule) (right := right) a => .twoPremise rule (doSubstitution a replacement) right
  | .right (rule := rule) (left := left) a => .twoPremise rule left (doSubstitution a replacement)

/-- Replace each leaf once, traversing the input tree rather than the
    newly inserted subtrees. This preserves the identities of equal leaves. -/
@[blueprint "chap3__definition_3_4_6"]
def mapLeaves (expand : (s : Sequent) → DeductionTree s) :
    {s : Sequent} → DeductionTree s → DeductionTree s
  | _, .leaf s => expand s
  | _, .onePremise rule child => .onePremise rule (mapLeaves expand child)
  | _, .twoPremise rule left right =>
    .twoPremise rule (mapLeaves expand left) (mapLeaves expand right)

-- ========= Definition 3.4.6: expandLeaf =========

/-- Definition 3.4.6 (companion): Finds the first nonatomic formula in a
    list, returning the formula and its index. -/
@[blueprint "chap3__definition_3_4_6"]
def findFirstNonatomic (L : List PropFormulaNormalized) (k : Nat := 0) :
    Option (PropFormulaNormalized × Nat) :=
  match L with
  | [] => none
  | A :: rest => if isNonatomicBool A then some (A, k) else findFirstNonatomic rest (k + 1)



/-- Definition 3.4.6 (required helper): If `findFirstNonatomic L = some (A, i)`,
    then `L = L.take i ++ [A] ++ L.drop (i+1)`. Enables `expandLeaf` to
    construct `DeductionTree s` by rewriting `s.antecedent` (resp. `s.succedent`)
    into its rule-shaped split form. -/
@[blueprint "chap3__definition_3_4_6"]
theorem findFirstNonatomic_split
    (ante : List PropFormulaNormalized) (A : PropFormulaNormalized) (i : Nat)
    (h : findFirstNonatomic ante = some (A, i)) :
    ante = ante.take i ++ [A] ++ ante.drop (i + 1) 

/-- Apply the rule at the selected occurrence on either side. The selectors
    certify the split around that occurrence. -/
@[blueprint "chap3__definition_3_4_6"]
def expandSelected (s : Sequent)
    (pickAnte pickSucc : Option (PropFormulaNormalized × Nat))
    (splitAnte : ∀ A i, pickAnte = some (A, i) →
      s.antecedent = s.antecedent.take i ++ [A] ++ s.antecedent.drop (i + 1))
    (splitSucc : ∀ A i, pickSucc = some (A, i) →
      s.succedent = s.succedent.take i ++ [A] ++ s.succedent.drop (i + 1)) : DeductionTree s :=
  match (generalizing := false) hAnte : pickAnte with
  | some (A, i) =>
    let gamma := s.antecedent.take i
    let delta := s.antecedent.drop (i + 1)
    let hsplit : s.antecedent = gamma ++ [A] ++ delta :=
      splitAnte A i hAnte
    let hseq : Sequent.mk (gamma ++ [A] ++ delta) s.succedent = s := by
      cases s with | mk ante succ => simp at hsplit; simp [hsplit.symm]
    match A, hseq with
    | .neg C, heq =>
      let prem : Sequent := Sequent.mk (gamma ++ delta) (C :: s.succedent)
      heq ▸ DeductionTree.onePremise (GentzenStep1.negLeft gamma delta s.succedent C)
        (DeductionTree.leaf prem)
    | .conj C D, heq =>
      let prem : Sequent := Sequent.mk (gamma ++ [C, D] ++ delta) s.succedent
      heq ▸ DeductionTree.onePremise (GentzenStep1.andLeft gamma delta s.succedent C D)
        (DeductionTree.leaf prem)
    | .disj C D, heq =>
      let p1 : Sequent := Sequent.mk (gamma ++ [C] ++ delta) s.succedent
      let p2 : Sequent := Sequent.mk (gamma ++ [D] ++ delta) s.succedent
      heq ▸ DeductionTree.twoPremise (GentzenStep2.orLeft gamma delta s.succedent C D)
        (DeductionTree.leaf p1) (DeductionTree.leaf p2)
    | .impl C D, heq =>
      let p1 : Sequent := Sequent.mk (gamma ++ delta) (C :: s.succedent)
      let p2 : Sequent := Sequent.mk ([D] ++ gamma ++ delta) s.succedent
      heq ▸ DeductionTree.twoPremise (GentzenStep2.implLeft gamma delta s.succedent C D)
        (DeductionTree.leaf p1) (DeductionTree.leaf p2)
    | .var _, _ => DeductionTree.leaf s
  | none =>
    match (generalizing := false) hSucc : pickSucc with
    | some (B, j) =>
      let delta := s.succedent.take j
      let lambda := s.succedent.drop (j + 1)
      let hsplit : s.succedent = delta ++ [B] ++ lambda :=
        splitSucc B j hSucc
      let hseq : Sequent.mk s.antecedent (delta ++ [B] ++ lambda) = s := by
        cases s with | mk ante succ => simp at hsplit; simp [hsplit.symm]
      match B, hseq with
      | .neg C, heq =>
        let prem : Sequent := Sequent.mk (C :: s.antecedent) (delta ++ lambda)
        heq ▸ DeductionTree.onePremise
          (GentzenStep1.negRight s.antecedent delta lambda C)
          (DeductionTree.leaf prem)
      | .conj C D, heq =>
        let p1 : Sequent := Sequent.mk s.antecedent (delta ++ [C] ++ lambda)
        let p2 : Sequent := Sequent.mk s.antecedent (delta ++ [D] ++ lambda)
        heq ▸ DeductionTree.twoPremise
          (GentzenStep2.andRight s.antecedent delta lambda C D)
          (DeductionTree.leaf p1) (DeductionTree.leaf p2)
      | .disj C D, heq =>
        let prem : Sequent := Sequent.mk s.antecedent (delta ++ [C, D] ++ lambda)
        heq ▸ DeductionTree.onePremise
          (GentzenStep1.orRight s.antecedent delta lambda C D)
          (DeductionTree.leaf prem)
      | .impl C D, heq =>
        let prem : Sequent := Sequent.mk (C :: s.antecedent) (D :: (delta ++ lambda))
        heq ▸ DeductionTree.onePremise
          (GentzenStep1.implRight s.antecedent delta lambda C D)
          (DeductionTree.leaf prem)
      | .var _, _ => DeductionTree.leaf s
    | none => DeductionTree.leaf s

/-- The first effective step of a round; preceding atomic occurrences do
    not generate rules. -/
@[blueprint "chap3__definition_3_4_6"]
def expandFirstFormula (s : Sequent) : DeductionTree s :=
  expandSelected s (findFirstNonatomic s.antecedent) (findFirstNonatomic s.succedent)
    (findFirstNonatomic_split s.antecedent) (findFirstNonatomic_split s.succedent)

end LCS.Propositional.Systems.G.Search
end

