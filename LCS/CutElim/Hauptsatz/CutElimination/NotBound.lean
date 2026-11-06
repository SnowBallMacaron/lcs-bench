import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.NotBound.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN.Variables
namespace FormulaN

/-- Definition 6.4.5: A variable y is not bound in formula A iff
y is not in BV(A), the set of bound variables of A. -/
@[blueprint "chap6__definition_6_4_5" (main := true)]
def notBoundIn {L : Language} (y : Nat) (A : FormulaN L) : Prop :=
  ¬ (formulaBVN A y)

end FormulaN
end LCS.FirstOrder.SyntaxN
namespace LCS.CutElim.Hauptsatz
namespace G1nnfDeductionTree

/-- Definition 6.4.5 (companion): Collects all formulae appearing in a G1nnf
    deduction tree (in every sequent position) as a `LCS.Finset`. Used in
    the body of `G1nnfDeductionTree.notBoundIn` to encode the textbook
    clause "y is not bound in the deduction tree T iff it is not bound in
    any sequent occurring in T". -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def allFormulae {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfDeductionTree hL Γ Δ → LCS.Finset (FormulaN L)
  | Γ, Δ, .leaf _ _ _ => LCS.Finset.union Γ Δ
  | _, _, .onePremise rule Γ Δ _ _ sub =>
      LCS.Finset.union (LCS.Finset.union (rule.conclusion Γ Δ).1
        (rule.conclusion Γ Δ).2) (allFormulae sub)
  | _, _, .twoPremise rule Γ Δ _ _ sub1 sub2 =>
      LCS.Finset.union (LCS.Finset.union (rule.conclusion Γ Δ).1
        (rule.conclusion Γ Δ).2)
        (LCS.Finset.union (allFormulae sub1) (allFormulae sub2))

/-- Definition 6.4.5 (companion): A variable y is not bound in deduction
    tree T iff y is not bound in any formula appearing in T. Textbook:
    "The variable y is not bound in the deduction tree T iff it is not
    bound in any sequent occurring in T." This faithfully typed version
    replaces the prior `G1nnfProofTree.notBoundIn` (which confused proof
    trees with deduction trees — the textbook intent). Specialize to
    proof trees via `T.forgetProofTree.notBoundIn y`. -/
@[blueprint "chap6__definition_6_4_5" (main := true)]
noncomputable def notBoundIn {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (y : Nat) (T : G1nnfDeductionTree hL Γ Δ) : Prop :=
  ∀ A, A ∈ allFormulae T → FormulaN.notBoundIn y A

end G1nnfDeductionTree
namespace G1nnfProofTree

/-- Definition 6.4.5 (proof-tree companion): all formulae in the actual
sequents of a proof tree. At a rule node this includes the indexed conclusion
and then every formula occurring in each premise subtree. In particular, an
axiom's stored side contexts are part of its actual indexed conclusion. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def allFormulae {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfProofTree hL Γ Δ → LCS.Finset (FormulaN L)
  | _, _, .axiom_ rule Γ Δ _ _ =>
      LCS.Finset.union (rule.conclusion Γ Δ).1
        (rule.conclusion Γ Δ).2
  | _, _, .onePremise rule Γ Δ _ _ sub =>
      LCS.Finset.union
        (LCS.Finset.union (rule.conclusion Γ Δ).1
          (rule.conclusion Γ Δ).2)
        (allFormulae sub)
  | _, _, .twoPremise rule Γ Δ _ _ sub1 sub2 =>
      LCS.Finset.union
        (LCS.Finset.union (rule.conclusion Γ Δ).1
          (rule.conclusion Γ Δ).2)
        (LCS.Finset.union (allFormulae sub1) (allFormulae sub2))

/-- Definition 6.4.5: a variable is not bound in a proof tree iff it is
not bound in any formula in any sequent of that tree. The quantifier is
restricted to `allFormulae T`, rather than ranging over unrelated provable
sequents. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def notBoundIn {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y : Nat) : Prop :=
  ∀ A, A ∈ T.allFormulae → FormulaN.notBoundIn y A

/-- Lemma 6.4.3 (structural helper): every antecedent formula at the root
occurs in `allFormulae T`. -/
theorem mem_allFormulae_of_mem_left {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (A : FormulaN L) (hA : A ∈ Γ) :
    A ∈ T.allFormulae := by
  cases T <;> simp_all [allFormulae]

/-- Lemma 6.4.3 (structural helper): every succedent formula at the root
occurs in `allFormulae T`. -/
theorem mem_allFormulae_of_mem_right {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (A : FormulaN L) (hA : A ∈ Δ) :
    A ∈ T.allFormulae := by
  cases T <;> simp_all [allFormulae]

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Hygiene
/-- Formulae in a one-premise subtree remain formulae of the whole tree. -/
theorem mem_allFormulae_onePremise_of_subtree {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 1)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (A : FormulaN L) (hA : A ∈ sub.allFormulae) :
    A ∈ (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC sub).allFormulae := by
  exact LCS.Finset.mem_union.mpr (Or.inr hA)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Hygiene
/-- Formulae in the first two-premise subtree remain formulae of the whole
tree. -/
theorem mem_allFormulae_twoPremise_left_of_subtree {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub1 : G1nnfProofTree hL ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (A : FormulaN L) (hA : A ∈ sub1.allFormulae) :
    A ∈ (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC
      sub1 sub2).allFormulae := by
  exact LCS.Finset.mem_union.mpr
    (Or.inr (LCS.Finset.mem_union.mpr (Or.inl hA)))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Hygiene
/-- Formulae in the second two-premise subtree remain formulae of the whole
tree. -/
theorem mem_allFormulae_twoPremise_right_of_subtree {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub1 : G1nnfProofTree hL ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (A : FormulaN L) (hA : A ∈ sub2.allFormulae) :
    A ∈ (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC
      sub1 sub2).allFormulae := by
  exact LCS.Finset.mem_union.mpr
    (Or.inr (LCS.Finset.mem_union.mpr (Or.inr hA)))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Hygiene
/-- Proof-wide non-binding projects to the root sequent. -/
theorem notBoundIn_atRoot {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y : Nat)
    (hNotBound : T.notBoundIn y) :
    (∀ A ∈ Γ, FormulaN.notBoundIn y A) ∧
    (∀ A ∈ Δ, FormulaN.notBoundIn y A) := by
  constructor
  · intro A hA
    exact hNotBound A (T.mem_allFormulae_of_mem_left A hA)
  · intro A hA
    exact hNotBound A (T.mem_allFormulae_of_mem_right A hA)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Hygiene
/-- Proof-wide non-binding projects to a one-premise subtree. -/
theorem notBoundIn_onePremise_subtree {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 1)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (y : Nat)
    (hNotBound :
      (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC sub).notBoundIn y) :
    sub.notBoundIn y := by
  intro A hA
  exact hNotBound A
    (mem_allFormulae_onePremise_of_subtree
      rule Γ Δ hPrem hAC sub A hA)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Freshening, LCS.CutElim.Hauptsatz.CutElimination.Hygiene
/-- Proof-wide non-binding projects to both two-premise subtrees. -/
theorem notBoundIn_twoPremise_subtrees {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub1 : G1nnfProofTree hL ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (y : Nat)
    (hNotBound :
      (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC
        sub1 sub2).notBoundIn y) :
    sub1.notBoundIn y ∧ sub2.notBoundIn y := by
  constructor
  · intro A hA
    exact hNotBound A
      (mem_allFormulae_twoPremise_left_of_subtree
        rule Γ Δ hPrem hAC sub1 sub2 A hA)
  · intro A hA
    exact hNotBound A
      (mem_allFormulae_twoPremise_right_of_subtree
        rule Γ Δ hPrem hAC sub1 sub2 A hA)

end G1nnfProofTree

/-- Definition 6.4.5 (substitution-lemma contract): a term `t` is free
for substitution for `y` in the root sequent `Γ → Δ`. Unlike
`G1nnfProofTree.freeForEverywhere`, this is exactly the root-only hypothesis
of Lemma 6.4.4. -/
@[blueprint "chap6__lemma_6_4_4"]
def freeForAtRoot {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (_ : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat) : Prop :=
  (∀ A ∈ Γ, isFreeForN t y A) ∧
  (∀ A ∈ Δ, isFreeForN t y A)

/-- If `y` is not bound in `A` and `t` is free for `y` in `A`, no
variable occurring in `t` is bound in `A`. This is the root-stability fact
used when proof-wide binder hygienization avoids `FV(t)`. -/
theorem FormulaN.notBoundIn_and_freeFor_termFV_not_bound {L : Language}
    (A : FormulaN L) (t : Term L) (y v : Nat)
    (hNotBound : A.notBoundIn y)
    (hFree : isFreeForN t y A)
    (hv : termFV t v) :
    v ∉ formulaBVN A := by
  induction A with
  | predN _ _ => exact id
  | eq_ _ _ => exact id
  | neg A ih =>
      exact ih hNotBound hFree
  | conj A B ihA ihB =>
      intro hBound
      exact hBound.elim
        (ihA (fun h => hNotBound (Or.inl h)) hFree.1)
        (ihB (fun h => hNotBound (Or.inr h)) hFree.2)
  | disj A B ihA ihB =>
      intro hBound
      exact hBound.elim
        (ihA (fun h => hNotBound (Or.inl h)) hFree.1)
        (ihB (fun h => hNotBound (Or.inr h)) hFree.2)
  | impl A B ihA ihB =>
      intro hBound
      exact hBound.elim
        (ihA (fun h => hNotBound (Or.inl h)) hFree.1)
        (ihB (fun h => hNotBound (Or.inr h)) hFree.2)
  | all x A ih =>
      have hyx : y ≠ x := fun h => hNotBound (Or.inr h)
      have hNotBoundA : A.notBoundIn y :=
        fun h => hNotBound (Or.inl h)
      rcases hFree with hEq | ⟨hxFresh, hFreeA⟩
      · exact absurd hEq hyx
      · intro hBound
        rcases hBound with hBoundA | hvx
        · exact ih hNotBoundA hFreeA hBoundA
        · subst v
          exact hxFresh hv
  | ex x A ih =>
      have hyx : y ≠ x := fun h => hNotBound (Or.inr h)
      have hNotBoundA : A.notBoundIn y :=
        fun h => hNotBound (Or.inl h)
      rcases hFree with hEq | ⟨hxFresh, hFreeA⟩
      · exact absurd hEq hyx
      · intro hBound
        rcases hBound with hBoundA | hvx
        · exact ih hNotBoundA hFreeA hBoundA
        · subst v
          exact hxFresh hv

end LCS.CutElim.Hauptsatz
end
