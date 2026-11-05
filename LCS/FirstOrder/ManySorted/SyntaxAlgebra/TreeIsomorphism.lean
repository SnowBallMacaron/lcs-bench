import LCS.FirstOrder.ManySorted.SyntaxAlgebra
import Attach
import LCS.FirstOrder.ManySorted.SyntaxAlgebra.TreeIsomorphism.ProofsStamp

/-! # The many-sorted tree algebra and its string isomorphism

Trees have sorted variable leaves and nodes labelled by the expanded
constructor signature. The isomorphism uses literal syntax, including the
sort and variable index of each quantifier.
-/

namespace LCS.FirstOrder.ManySorted.SyntaxAlgebra

open LCS.FirstOrder.ManySorted.CongruenceClosure

/-- Theorem 10.2.1 (companion): Finite ranked trees over V. Every node
has exactly the ordered input sorts and output sort of its constructor. -/
@[blueprint "chap10__theorem_10_2_1"]
inductive MSSyntaxTree (L : MSLanguage) : MSSyntaxSort L → Type where
  | var (s : L.SortType) (i : Nat) : MSSyntaxTree L (some s)
  | node (op : MSConstructorSymbol L)
      (children : (i : Fin ((msConstructorAlphabet L).argSorts op).length) →
        MSSyntaxTree L (((msConstructorAlphabet L).argSorts op).get i)) :
      MSSyntaxTree L ((msConstructorAlphabet L).resultSort op)

/-- Theorem 10.2.1 (companion): T_L(V), with node formation as its
operations. A variable inhabits every data carrier and bottom inhabits bool. -/
@[blueprint "chap10__theorem_10_2_1"]
def msTreeAlgebra (L : MSLanguage) :
    LCS.FirstOrder.Syntax.Algebra.MSAlgebra (msConstructorAlphabet L) where
  carrier := MSSyntaxTree L
  carrierNonempty := by
    intro s
    cases s with
    | some s => exact ⟨.var s 0⟩
    | none => exact ⟨.node .falsum (fun i => Fin.elim0 i)⟩
  operation := MSSyntaxTree.node

/-- Theorem 10.2.1 (companion): The tree A_i^s(A), with one bool child. -/
@[blueprint "chap10__theorem_10_2_1"]
def msUniversalTree {L : MSLanguage} (s : L.SortType) (i : Nat)
    (A : MSSyntaxTree L none) : MSSyntaxTree L none :=
  .node (.all s i) (fun j => by
    have hj : j = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (by
      change j.val = 0
      have h := j.isLt
      change j.val < 1 at h
      omega)
    subst j
    exact A)

/-- Theorem 10.2.1 (companion): The tree E_i^s(A), with one bool child. -/
@[blueprint "chap10__theorem_10_2_1"]
def msExistentialTree {L : MSLanguage} (s : L.SortType) (i : Nat)
    (A : MSSyntaxTree L none) : MSSyntaxTree L none :=
  .node (.ex s i) (fun j => by
    have hj : j = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (by
      change j.val = 0
      have h := j.isLt
      change j.val < 1 at h
      omega)
    subst j
    exact A)

/-- Theorem 10.2.1 (companion): The universal string operation on T(L,V),
whose underlying token list is ∀ₛ xᵢ followed by the body string. -/
@[blueprint "chap10__theorem_10_2_1"]
def msGeneratedAll {L : MSLanguage} (s : L.SortType) (i : Nat)
    (A : (msGeneratedStringAlgebra L).carrier none) :
    (msGeneratedStringAlgebra L).carrier none :=
  (msGeneratedStringAlgebra L).operation (.all s i) (fun j => by
    have hj : j = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (by
      change j.val = 0
      have h := j.isLt
      change j.val < 1 at h
      omega)
    subst j
    exact A)

/-- Theorem 10.2.1 (companion): The existential string operation on T(L,V),
whose underlying token list is ∃ₛ xᵢ followed by the body string. -/
@[blueprint "chap10__theorem_10_2_1"]
def msGeneratedEx {L : MSLanguage} (s : L.SortType) (i : Nat)
    (A : (msGeneratedStringAlgebra L).carrier none) :
    (msGeneratedStringAlgebra L).carrier none :=
  (msGeneratedStringAlgebra L).operation (.ex s i) (fun j => by
    have hj : j = ⟨0, by change 0 < 1; decide⟩ := Fin.ext (by
      change j.val = 0
      have h := j.isLt
      change j.val < 1 at h
      omega)
    subst j
    exact A)

/-- Theorem 10.2.1 (companion): One sortwise bijective homomorphism from
the generated string algebra to the tree algebra, with a homomorphic inverse.
It fixes V and satisfies both quantifier-node equations for that same map. -/
@[attach_debt, blueprint "chap10__theorem_10_2_1"]
theorem msString_tree_isomorphism (L : MSLanguage) :
    ∃ (f : (s : MSSyntaxSort L) → (msGeneratedStringAlgebra L).carrier s → MSSyntaxTree L s)
      (g : (s : MSSyntaxSort L) → MSSyntaxTree L s → (msGeneratedStringAlgebra L).carrier s),
      MSExpandedHom (msGeneratedStringAlgebra L) (msTreeAlgebra L) f ∧
      MSExpandedHom (msTreeAlgebra L) (msGeneratedStringAlgebra L) g ∧
      MSVariableRestriction (msTreeAlgebra L) MSSyntaxTree.var f ∧
      (∀ s x, g s (f s x) = x) ∧ (∀ s t, f s (g s t) = t) ∧
      (∀ s, Function.Injective (f s) ∧ ∀ t, ∃ x, f s x = t) ∧
      (∀ s i A, f none (msGeneratedAll s i A) = msUniversalTree s i (f none A)) ∧
      (∀ s i A, f none (msGeneratedEx s i A) = msExistentialTree s i (f none A))

end LCS.FirstOrder.ManySorted.SyntaxAlgebra
