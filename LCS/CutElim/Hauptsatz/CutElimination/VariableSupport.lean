import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.Trees
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem LCS.Finset.image_insert [DecidableEq α] [DecidableEq β]
    (f : α → β) (a : α) (s : LCS.Finset α) :
    LCS.Finset.image f (LCS.Finset.insert a s) =
      LCS.Finset.insert (f a) (LCS.Finset.image f s) := by
-- BEGIN PROOF
  apply LCS.Finset.ext; intro b
  rw [LCS.Finset.mem_image, LCS.Finset.mem_insert]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LCS.Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (LCS.Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  · rintro (rfl | hb)
    · exact ⟨a, LCS.Finset.mem_insert.mpr (Or.inl rfl), rfl⟩
    · obtain ⟨x, hx, rfl⟩ := LCS.Finset.mem_image.mp hb
      exact ⟨x, LCS.Finset.mem_insert.mpr (Or.inr hx), rfl⟩

end

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
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
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
end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
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

/-- Definition 6.4.5 (internal companion): a term is free for `y` in
every formula in every sequent of the proof tree. This is the proof-wide
hypothesis used by Lemma 6.4.3(ii), not the root-only hypothesis of the
public substitution lemma. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def freeForEverywhere {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat) : Prop :=
  ∀ A, A ∈ T.allFormulae → isFreeForN t y A

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Lemma 6.4.3 (structural helper): every antecedent formula at the root
occurs in `allFormulae T`. -/
theorem mem_allFormulae_of_mem_left {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (A : FormulaN L) (hA : A ∈ Γ) :
    A ∈ T.allFormulae := by
  cases T <;> simp_all [allFormulae]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Proof-wide freeness implies freeness in the root sequent. -/
theorem freeForEverywhere_atRoot {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat)
    (hFree : T.freeForEverywhere t y) :
    (∀ A ∈ Γ, isFreeForN t y A) ∧
    (∀ A ∈ Δ, isFreeForN t y A) := by
  constructor
  · intro A hA
    exact hFree A (T.mem_allFormulae_of_mem_left A hA)
  · intro A hA
    exact hFree A (T.mem_allFormulae_of_mem_right A hA)

end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

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

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem G1nnfProofTree.freeForAtRoot_of_freeForEverywhere {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat)
    (hFree : T.freeForEverywhere t y) :
    freeForAtRoot T t y :=
  T.freeForEverywhere_atRoot t y hFree

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Antecedent projection of the root free-for contract. -/
theorem G1nnfProofTree.freeForAtRoot_left {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat)
    (hFree : freeForAtRoot T t y) :
    ∀ A ∈ Γ, isFreeForN t y A :=
  hFree.1

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Succedent projection of the root free-for contract. -/
theorem G1nnfProofTree.freeForAtRoot_right {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat)
    (hFree : freeForAtRoot T t y) :
    ∀ A ∈ Δ, isFreeForN t y A :=
  hFree.2

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
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

-- ===================================================================
-- Definition 6.4.5 (finite helper): proof-wide variable support
-- ===================================================================

/-- All variable indices occurring in a term. -/
@[blueprint "chap6__definition_6_4_5"]
def termVariableSupport {L : Language} (t : Term L) : LCS.Finset Nat :=
  LCS.Finset.ofList (termVarIndicesList t)

/-- A duplicate-tolerant structural enumeration of every variable in a
formula, including variables in terms and every quantifier binder. -/
@[blueprint "chap6__definition_6_4_5"]
def formulaVariableIndices {L : Language} : FormulaN L → List Nat
  | .predN P ts =>
      (List.ofFn fun i : Fin (L.predArity P) => i).foldl
        (fun acc i => acc ++ termVarIndicesList (ts i)) []
  | .eq_ _ t₁ t₂ => termVarIndicesList t₁ ++ termVarIndicesList t₂
  | .neg A => formulaVariableIndices A
  | .conj A B => formulaVariableIndices A ++ formulaVariableIndices B
  | .disj A B => formulaVariableIndices A ++ formulaVariableIndices B
  | .impl A B => formulaVariableIndices A ++ formulaVariableIndices B
  | .all x A => x :: formulaVariableIndices A
  | .ex x A => x :: formulaVariableIndices A

/-- All free and bound variable indices occurring in a formula. -/
@[blueprint "chap6__definition_6_4_5"]
def formulaVariableSupport {L : Language}
    (A : FormulaN L) : LCS.Finset Nat :=
  LCS.Finset.ofList (formulaVariableIndices A)

/-- The finite union of the variable supports of a Finset of formulae. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def formulaFinsetVariableSupport {L : Language}
    (S : LCS.Finset (FormulaN L)) : LCS.Finset Nat :=
  LCS.Finset.ofList
    (S.toList.flatMap formulaVariableIndices)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Freshening
/-- Membership in the term-variable accumulator used by
`termVarIndicesList`. -/
theorem mem_foldl_append_termVariableIndices {L : Language}
    (v : Nat) {β : Type} (f : β → Term L) :
    ∀ (indices : List β) (acc : List Nat),
      v ∈ indices.foldl
          (fun vars i => vars ++ termVarIndicesList (f i)) acc ↔
        v ∈ acc ∨ ∃ i ∈ indices, v ∈ termVarIndicesList (f i) := by
  intro indices
  induction indices with
  | nil =>
      intro acc
      simp
  | cons i indices ih =>
      intro acc
      simp only [List.foldl]
      rw [ih]
      simp only [List.mem_append, List.mem_cons]
      constructor
      · rintro ((hv | hv) | ⟨j, hj, hv⟩)
        · exact Or.inl hv
        · exact Or.inr ⟨i, Or.inl rfl, hv⟩
        · exact Or.inr ⟨j, Or.inr hj, hv⟩
      · rintro (hv | ⟨j, rfl | hj, hv⟩)
        · exact Or.inl (Or.inl hv)
        · exact Or.inl (Or.inr hv)
        · exact Or.inr ⟨j, hj, hv⟩

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Freshening
/-- `termVariableSupport` contains exactly the variables occurring in the
term, stated in the direction used by fresh-variable construction. -/
theorem termFV_mem_termVariableSupport {L : Language}
    (t : Term L) (v : Nat) (hv : termFV t v) :
    v ∈ termVariableSupport t := by
  rw [termVariableSupport, LCS.Finset.mem_ofList]
  induction t with
  | var x =>
      change v = x at hv
      simpa [termVarIndicesList] using hv
  | const c =>
      exact hv.elim
  | func f ts ih =>
      rcases hv with ⟨i, hi⟩
      apply
        (mem_foldl_append_termVariableIndices v ts
          (List.ofFn fun i : Fin (L.funArity f) => i) []).2
      exact Or.inr
        ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, ih i hi⟩

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Every free variable of a formula is in its finite structural support. -/
theorem formulaFVN_mem_formulaVariableSupport {L : Language}
    (A : FormulaN L) (v : Nat) (hv : formulaFVN A v) :
    v ∈ formulaVariableSupport A := by
  rw [formulaVariableSupport, LCS.Finset.mem_ofList]
  induction A with
  | predN P ts =>
      rcases hv with ⟨i, hi⟩
      apply
        (mem_foldl_append_termVariableIndices v ts
          (List.ofFn fun i : Fin (L.predArity P) => i) []).2
      exact Or.inr
        ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩,
          (LCS.Finset.mem_ofList.mp
            (termFV_mem_termVariableSupport (ts i) v hi))⟩
  | eq_ h t₁ t₂ =>
      rcases hv with hv | hv
      · exact List.mem_append_left _
          (LCS.Finset.mem_ofList.mp
            (termFV_mem_termVariableSupport t₁ v hv))
      · exact List.mem_append_right _
          (LCS.Finset.mem_ofList.mp
            (termFV_mem_termVariableSupport t₂ v hv))
  | neg A ih => exact ih hv
  | conj A B ihA ihB =>
      exact hv.elim
        (fun h => List.mem_append_left _ (ihA h))
        (fun h => List.mem_append_right _ (ihB h))
  | disj A B ihA ihB =>
      exact hv.elim
        (fun h => List.mem_append_left _ (ihA h))
        (fun h => List.mem_append_right _ (ihB h))
  | impl A B ihA ihB =>
      exact hv.elim
        (fun h => List.mem_append_left _ (ihA h))
        (fun h => List.mem_append_right _ (ihB h))
  | all x A ih =>
      exact List.mem_cons.mpr (Or.inr (ih hv.1))
  | ex x A ih =>
      exact List.mem_cons.mpr (Or.inr (ih hv.1))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every bound variable of a formula is in its finite structural support. -/
theorem formulaBVN_mem_formulaVariableSupport {L : Language}
    (A : FormulaN L) (v : Nat) (hv : formulaBVN A v) :
    v ∈ formulaVariableSupport A := by
  rw [formulaVariableSupport, LCS.Finset.mem_ofList]
  induction A with
  | predN _ _ => exact hv.elim
  | eq_ _ _ => exact hv.elim
  | neg A ih => exact ih hv
  | conj A B ihA ihB =>
      exact hv.elim
        (fun h => List.mem_append_left _ (ihA h))
        (fun h => List.mem_append_right _ (ihB h))
  | disj A B ihA ihB =>
      exact hv.elim
        (fun h => List.mem_append_left _ (ihA h))
        (fun h => List.mem_append_right _ (ihB h))
  | impl A B ihA ihB =>
      exact hv.elim
        (fun h => List.mem_append_left _ (ihA h))
        (fun h => List.mem_append_right _ (ihB h))
  | all x A ih =>
      exact hv.elim
        (fun h => List.mem_cons.mpr (Or.inr (ih h)))
        (fun h => List.mem_cons.mpr (Or.inl h))
  | ex x A ih =>
      exact hv.elim
        (fun h => List.mem_cons.mpr (Or.inr (ih h)))
        (fun h => List.mem_cons.mpr (Or.inl h))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Formula support is included in the support of any formula Finset that
contains it. -/
theorem formulaVariableSupport_subset_finsetSupport {L : Language}
    (S : LCS.Finset (FormulaN L)) (A : FormulaN L) (v : Nat)
    (hA : A ∈ S) (hv : v ∈ formulaVariableSupport A) :
    v ∈ formulaFinsetVariableSupport S := by
  rw [formulaFinsetVariableSupport, LCS.Finset.mem_ofList,
    List.mem_flatMap]
  exact ⟨A, (LCS.Finset.mem_toList S A).2 hA,
    LCS.Finset.mem_ofList.mp hv⟩

-- retained: used by LCS.Herbrand.NNFHauptsatz.Theorem.VariableSupport
/-- Membership in a formula-Finset support comes from one of its formulae. -/
theorem mem_formulaFinsetVariableSupport_iff {L : Language}
    (S : LCS.Finset (FormulaN L)) (v : Nat) :
    v ∈ formulaFinsetVariableSupport S ↔
      ∃ A ∈ S, v ∈ formulaVariableSupport A := by
  rw [formulaFinsetVariableSupport, LCS.Finset.mem_ofList,
    List.mem_flatMap]
  constructor
  · rintro ⟨A, hA, hv⟩
    exact ⟨A, (LCS.Finset.mem_toList S A).1 hA,
      LCS.Finset.mem_ofList.mpr hv⟩
  · rintro ⟨A, hA, hv⟩
    exact ⟨A, (LCS.Finset.mem_toList S A).2 hA,
      LCS.Finset.mem_ofList.mp hv⟩

end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfRule

/-- The full finite support of the data stored by a rule: principal and cut
formulae, stored axiom and cut contexts, quantifier binders, eigenvariable labels, and
instantiation terms. Residual node contexts are collected separately by the
proof-tree support below. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def variableSupport {L : Language} :
    G1nnfRule L → LCS.Finset Nat
  | .axiomPosAtomic A _ Γ Δ =>
      LCS.Finset.union (formulaVariableSupport A)
        (LCS.Finset.union (formulaFinsetVariableSupport Γ)
          (formulaFinsetVariableSupport Δ))
  | .axiomNegAtomic A _ Γ Δ =>
      LCS.Finset.union (formulaVariableSupport A)
        (LCS.Finset.union (formulaFinsetVariableSupport Γ)
          (formulaFinsetVariableSupport Δ))
  | .axiomCompLeft A _ Γ Δ =>
      LCS.Finset.union (formulaVariableSupport A)
        (LCS.Finset.union (formulaFinsetVariableSupport Γ)
          (formulaFinsetVariableSupport Δ))
  | .axiomCompRight A _ Γ Δ =>
      LCS.Finset.union (formulaVariableSupport A)
        (LCS.Finset.union (formulaFinsetVariableSupport Γ)
          (formulaFinsetVariableSupport Δ))
  | .cut A Lam Theta =>
      LCS.Finset.union (formulaVariableSupport A)
        (LCS.Finset.union (formulaFinsetVariableSupport Lam)
          (formulaFinsetVariableSupport Theta))
  | .conjLeft1 A B =>
      LCS.Finset.union (formulaVariableSupport A) (formulaVariableSupport B)
  | .conjLeft2 A B =>
      LCS.Finset.union (formulaVariableSupport A) (formulaVariableSupport B)
  | .conjRight A B =>
      LCS.Finset.union (formulaVariableSupport A) (formulaVariableSupport B)
  | .disjLeft A B =>
      LCS.Finset.union (formulaVariableSupport A) (formulaVariableSupport B)
  | .disjRight1 A B =>
      LCS.Finset.union (formulaVariableSupport A) (formulaVariableSupport B)
  | .disjRight2 A B =>
      LCS.Finset.union (formulaVariableSupport A) (formulaVariableSupport B)
  | .allLeft x A t =>
      LCS.Finset.insert x
        (LCS.Finset.union (formulaVariableSupport A) (termVariableSupport t))
  | .allRight x A ev =>
      LCS.Finset.insert x
        (LCS.Finset.insert ev (formulaVariableSupport A))
  | .exLeft x A ev =>
      LCS.Finset.insert x
        (LCS.Finset.insert ev (formulaVariableSupport A))
  | .exRight x A t =>
      LCS.Finset.insert x
        (LCS.Finset.union (formulaVariableSupport A) (termVariableSupport t))



-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Universal-left binder labels are in rule support. -/
theorem variableSupport_allLeft_binder {L : Language}
    (x : Nat) (A : FormulaN L) (t : Term L) :
    x ∈ (G1nnfRule.allLeft x A t).variableSupport :=
  LCS.Finset.mem_insert.mpr (Or.inl rfl)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Universal-left principal-formula variables are in rule support. -/
theorem variableSupport_allLeft_formula {L : Language}
    (x : Nat) (A : FormulaN L) (t : Term L) (v : Nat)
    (hv : v ∈ formulaVariableSupport A) :
    v ∈ (G1nnfRule.allLeft x A t).variableSupport :=
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_union.mpr (Or.inl hv)))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Universal-left instantiation-term variables are in rule support. -/
theorem variableSupport_allLeft_term {L : Language}
    (x : Nat) (A : FormulaN L) (t : Term L) (v : Nat)
    (hv : termFV t v) :
    v ∈ (G1nnfRule.allLeft x A t).variableSupport :=
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_union.mpr
      (Or.inr (termFV_mem_termVariableSupport t v hv))))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Universal-right binder labels are in rule support. -/
theorem variableSupport_allRight_binder {L : Language}
    (x ev : Nat) (A : FormulaN L) :
    x ∈ (G1nnfRule.allRight x A ev).variableSupport :=
  LCS.Finset.mem_insert.mpr (Or.inl rfl)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Universal-right eigenvariable labels are in rule support. -/
theorem variableSupport_allRight_eigenvariable {L : Language}
    (x ev : Nat) (A : FormulaN L) :
    ev ∈ (G1nnfRule.allRight x A ev).variableSupport :=
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_insert.mpr (Or.inl rfl)))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Universal-right principal-formula variables are in rule support. -/
theorem variableSupport_allRight_formula {L : Language}
    (x ev : Nat) (A : FormulaN L) (v : Nat)
    (hv : v ∈ formulaVariableSupport A) :
    v ∈ (G1nnfRule.allRight x A ev).variableSupport :=
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_insert.mpr (Or.inr hv)))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Existential-left binder labels are in rule support. -/
theorem variableSupport_exLeft_binder {L : Language}
    (x ev : Nat) (A : FormulaN L) :
    x ∈ (G1nnfRule.exLeft x A ev).variableSupport :=
  LCS.Finset.mem_insert.mpr (Or.inl rfl)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Existential-left eigenvariable labels are in rule support. -/
theorem variableSupport_exLeft_eigenvariable {L : Language}
    (x ev : Nat) (A : FormulaN L) :
    ev ∈ (G1nnfRule.exLeft x A ev).variableSupport :=
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_insert.mpr (Or.inl rfl)))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Existential-left principal-formula variables are in rule support. -/
theorem variableSupport_exLeft_formula {L : Language}
    (x ev : Nat) (A : FormulaN L) (v : Nat)
    (hv : v ∈ formulaVariableSupport A) :
    v ∈ (G1nnfRule.exLeft x A ev).variableSupport :=
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_insert.mpr (Or.inr hv)))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Existential-right binder labels are in rule support. -/
theorem variableSupport_exRight_binder {L : Language}
    (x : Nat) (A : FormulaN L) (t : Term L) :
    x ∈ (G1nnfRule.exRight x A t).variableSupport :=
  LCS.Finset.mem_insert.mpr (Or.inl rfl)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Existential-right principal-formula variables are in rule support. -/
theorem variableSupport_exRight_formula {L : Language}
    (x : Nat) (A : FormulaN L) (t : Term L) (v : Nat)
    (hv : v ∈ formulaVariableSupport A) :
    v ∈ (G1nnfRule.exRight x A t).variableSupport :=
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_union.mpr (Or.inl hv)))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- Existential-right instantiation-term variables are in rule support. -/
theorem variableSupport_exRight_term {L : Language}
    (x : Nat) (A : FormulaN L) (t : Term L) (v : Nat)
    (hv : termFV t v) :
    v ∈ (G1nnfRule.exRight x A t).variableSupport :=
  LCS.Finset.mem_insert.mpr
    (Or.inr (LCS.Finset.mem_union.mpr
      (Or.inr (termFV_mem_termVariableSupport t v hv))))

end G1nnfRule
end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfProofTree

/-- The finite support of rule data throughout a proof tree. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def ruleDataVariableSupport {L : Language} {hL : L.withoutEquality} :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G1nnfProofTree hL Γ Δ → LCS.Finset Nat
  | _, _, .axiom_ rule _ _ _ _ => rule.variableSupport
  | _, _, .onePremise rule _ _ _ _ sub =>
      LCS.Finset.union rule.variableSupport sub.ruleDataVariableSupport
  | _, _, .twoPremise rule _ _ _ _ sub1 sub2 =>
      LCS.Finset.union rule.variableSupport
        (LCS.Finset.union sub1.ruleDataVariableSupport
          sub2.ruleDataVariableSupport)

/-- Definition 6.4.5 (finite helper): the full proof-wide variable support.
The left summand covers every actual sequent; the right summand additionally
covers hidden structural rule data, including cut formulae, binders,
eigenvariable labels, instantiation terms, and stored axiom contexts. -/
@[blueprint "chap6__definition_6_4_5"]
noncomputable def variableSupport {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) : LCS.Finset Nat :=
  LCS.Finset.union (formulaFinsetVariableSupport T.allFormulae)
    T.ruleDataVariableSupport

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Formula support from any actual proof-tree sequent is included in the
complete proof-wide support. -/
theorem variableSupport_of_formula_mem_allFormulae {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (A : FormulaN L) (v : Nat)
    (hA : A ∈ T.allFormulae) (hv : v ∈ formulaVariableSupport A) :
    v ∈ T.variableSupport :=
  LCS.Finset.mem_union.mpr
    (Or.inl (formulaVariableSupport_subset_finsetSupport
      T.allFormulae A v hA hv))

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every variable in recursively collected rule data is included in the
complete proof-wide support. -/
theorem variableSupport_of_ruleData {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (v : Nat)
    (hv : v ∈ T.ruleDataVariableSupport) :
    v ∈ T.variableSupport :=
  LCS.Finset.mem_union.mpr (Or.inr hv)

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- The rule data at an axiom node is included in the whole tree support. -/
theorem variableSupport_axiom_of_rule {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hAxiom : (rule.premises Γ Δ).length = 0)
    (hAC : rule.ApplicationConditions Γ Δ)
    (v : Nat) (hv : v ∈ rule.variableSupport) :
    v ∈ (G1nnfProofTree.axiom_ (hL := hL) rule Γ Δ hAxiom hAC).variableSupport :=
  (G1nnfProofTree.axiom_ (hL := hL) rule Γ Δ hAxiom hAC).variableSupport_of_ruleData
    v hv

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- The rule data at a one-premise node is included in the whole tree
support. -/
theorem variableSupport_onePremise_of_rule {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 1)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (v : Nat) (hv : v ∈ rule.variableSupport) :
    v ∈ (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC
      sub).variableSupport :=
  (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC sub
    ).variableSupport_of_ruleData v
      (LCS.Finset.mem_union.mpr (Or.inl hv))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- The subtree support of a one-premise node is included in the whole tree
support. -/
theorem variableSupport_onePremise_of_subtree {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 1)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (v : Nat) (hv : v ∈ sub.variableSupport) :
    v ∈ (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC
      sub).variableSupport := by
  rcases LCS.Finset.mem_union.mp hv with hv | hv
  · obtain ⟨A, hA, hvA⟩ :=
      (mem_formulaFinsetVariableSupport_iff sub.allFormulae v).1 hv
    exact
      (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC sub
        ).variableSupport_of_formula_mem_allFormulae A v
          (mem_allFormulae_onePremise_of_subtree
            rule Γ Δ hPrem hAC sub A hA) hvA
  · exact
      (G1nnfProofTree.onePremise rule Γ Δ hPrem hAC sub
        ).variableSupport_of_ruleData v
          (LCS.Finset.mem_union.mpr (Or.inr hv))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- The rule data at a two-premise node is included in the whole tree
support. -/
theorem variableSupport_twoPremise_of_rule {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub1 : G1nnfProofTree hL ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (v : Nat) (hv : v ∈ rule.variableSupport) :
    v ∈ (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC
      sub1 sub2).variableSupport :=
  (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC sub1 sub2
    ).variableSupport_of_ruleData v
      (LCS.Finset.mem_union.mpr (Or.inl hv))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- The first subtree support of a two-premise node is included in the whole
tree support. -/
theorem variableSupport_twoPremise_of_left_subtree {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub1 : G1nnfProofTree hL ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (v : Nat) (hv : v ∈ sub1.variableSupport) :
    v ∈ (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC
      sub1 sub2).variableSupport := by
  rcases LCS.Finset.mem_union.mp hv with hv | hv
  · obtain ⟨A, hA, hvA⟩ :=
      (mem_formulaFinsetVariableSupport_iff sub1.allFormulae v).1 hv
    exact
      (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC sub1 sub2
        ).variableSupport_of_formula_mem_allFormulae A v
          (mem_allFormulae_twoPremise_left_of_subtree
            rule Γ Δ hPrem hAC sub1 sub2 A hA) hvA
  · exact
      (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC sub1 sub2
        ).variableSupport_of_ruleData v
          (LCS.Finset.mem_union.mpr
            (Or.inr (LCS.Finset.mem_union.mpr (Or.inl hv))))

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.Substitution, LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
/-- The second subtree support of a two-premise node is included in the whole
tree support. -/
theorem variableSupport_twoPremise_of_right_subtree {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L) (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub1 : G1nnfProofTree hL ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (v : Nat) (hv : v ∈ sub2.variableSupport) :
    v ∈ (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC
      sub1 sub2).variableSupport := by
  rcases LCS.Finset.mem_union.mp hv with hv | hv
  · obtain ⟨A, hA, hvA⟩ :=
      (mem_formulaFinsetVariableSupport_iff sub2.allFormulae v).1 hv
    exact
      (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC sub1 sub2
        ).variableSupport_of_formula_mem_allFormulae A v
          (mem_allFormulae_twoPremise_right_of_subtree
            rule Γ Δ hPrem hAC sub1 sub2 A hA) hvA
  · exact
      (G1nnfProofTree.twoPremise rule Γ Δ hPrem hAC sub1 sub2
        ).variableSupport_of_ruleData v
          (LCS.Finset.mem_union.mpr
            (Or.inr (LCS.Finset.mem_union.mpr (Or.inr hv))))

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A deterministic variable strictly above every index in the finite
proof-wide support and an additional finite avoidance set. -/
noncomputable def freshVariableAvoiding {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (extra : LCS.Finset Nat) : Nat :=
  (LCS.Finset.union T.variableSupport extra).toList.foldl Nat.max 0 + 1

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The tree-only specialization of `freshVariableAvoiding`. -/
noncomputable def freshVariable {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) : Nat :=
  T.freshVariableAvoiding LCS.Finset.empty

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem foldl_max_init_le (xs : List Nat) (init : Nat) :
    init ≤ xs.foldl Nat.max init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      exact Nat.le_trans (Nat.le_max_left init x) (ih _)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem foldl_max_mem_le (xs : List Nat) (init v : Nat)
    (hv : v ∈ xs) : v ≤ xs.foldl Nat.max init := by
  induction xs generalizing init with
  | nil => simp at hv
  | cons x xs ih =>
      rcases List.mem_cons.mp hv with hvx | hv
      · subst v
        exact Nat.le_trans (Nat.le_max_right init x)
          (foldl_max_init_le xs (Nat.max init x))
      · exact ih (Nat.max init x) hv

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- The avoiding selector is outside the complete proof-wide support. -/
theorem freshVariableAvoiding_not_mem_variableSupport {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (extra : LCS.Finset Nat) :
    T.freshVariableAvoiding extra ∉ T.variableSupport := by
  intro hFresh
  have hList :
      T.freshVariableAvoiding extra ∈
        (LCS.Finset.union T.variableSupport extra).toList :=
    (LCS.Finset.mem_toList
      (LCS.Finset.union T.variableSupport extra)
      (T.freshVariableAvoiding extra)).2
      (LCS.Finset.mem_union.mpr (Or.inl hFresh))
  have hLe := foldl_max_mem_le
    (LCS.Finset.union T.variableSupport extra).toList 0
    (T.freshVariableAvoiding extra) hList
  simp only [freshVariableAvoiding] at hLe
  omega

-- retained: used by LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening, LCS.CutElim.Hauptsatz.CutElimination.Freshening
/-- The avoiding selector is outside the additional finite avoidance set. -/
theorem freshVariableAvoiding_not_mem_extra {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (extra : LCS.Finset Nat) :
    T.freshVariableAvoiding extra ∉ extra := by
  intro hFresh
  have hList :
      T.freshVariableAvoiding extra ∈
        (LCS.Finset.union T.variableSupport extra).toList :=
    (LCS.Finset.mem_toList
      (LCS.Finset.union T.variableSupport extra)
      (T.freshVariableAvoiding extra)).2
      (LCS.Finset.mem_union.mpr (Or.inr hFresh))
  have hLe := foldl_max_mem_le
    (LCS.Finset.union T.variableSupport extra).toList 0
    (T.freshVariableAvoiding extra) hList
  simp only [freshVariableAvoiding] at hLe
  omega



-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A selected variable is not bound anywhere in the tree. This gives a
concrete inhabitant of the non-vacuous `notBoundIn` predicate for every proof
tree and every additional avoidance set. -/
theorem freshVariableAvoiding_notBoundIn {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (extra : LCS.Finset Nat) :
    T.notBoundIn (T.freshVariableAvoiding extra) := by
  intro A hA hBound
  apply T.freshVariableAvoiding_not_mem_variableSupport extra
  exact T.variableSupport_of_formula_mem_allFormulae A
    (T.freshVariableAvoiding extra) hA
    (formulaBVN_mem_formulaVariableSupport A
      (T.freshVariableAvoiding extra) hBound)



end G1nnfProofTree
end LCS.CutElim.Hauptsatz
end

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Adversarial check: bound-variable capture in an axiom's actual side
context is detected by the proof-wide `notBoundIn` predicate. -/
theorem G1nnfProofTree.notBoundIn_axiomContext_rejects_capture
    {L : Language} {hL : L.withoutEquality} (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hAxiom : (rule.premises Γ Δ).length = 0)
    (hAC : rule.ApplicationConditions Γ Δ)
    (C : FormulaN L) (y : Nat)
    (hC :
      C ∈ (rule.conclusion Γ Δ).1 ∨
      C ∈ (rule.conclusion Γ Δ).2)
    (hy : formulaBVN C y) :
    ¬ (G1nnfProofTree.axiom_ (hL := hL) rule Γ Δ hAxiom hAC).notBoundIn y := by
  intro hNotBound
  have hMem :
      C ∈ (G1nnfProofTree.axiom_ (hL := hL) rule Γ Δ hAxiom hAC).allFormulae := by
    simp only [G1nnfProofTree.allFormulae, LCS.Finset.mem_union]
    exact hC
  exact (hNotBound C hMem) hy

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Adversarial check: an inner existential binder is still seen beneath an
outer universal binder; checking only the outer constructor would miss it. -/
theorem G1nnfProofTree.notBoundIn_rejects_nestedBinder
    {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (outer inner : Nat) (A : FormulaN L)
    (hNested : FormulaN.all outer (.ex inner A) ∈ Γ) :
    ¬ T.notBoundIn inner := by
  intro hNotBound
  have hMem :=
    T.mem_allFormulae_of_mem_left (.all outer (.ex inner A)) hNested
  apply hNotBound (.all outer (.ex inner A)) hMem
  exact Or.inl (Or.inr rfl)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Adversarial check: root freeness rejects capture by an inner binder of
a nested quantified formula. -/
theorem G1nnfProofTree.freeForAtRoot_rejects_nestedCapture
    {L : Language} {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (x outer inner : Nat) (A : FormulaN L)
    (hxOuter : x ≠ outer) (hxInner : x ≠ inner)
    (hNested : FormulaN.all outer (.ex inner A) ∈ Γ) :
    ¬ freeForAtRoot T (.var inner) x := by
  intro hFree
  have hFormula := hFree.1 (.all outer (.ex inner A)) hNested
  simp only [isFreeForN] at hFormula
  rcases hFormula with hEqOuter | ⟨_, hInner⟩
  · exact hxOuter hEqOuter
  · rcases hInner with hEqInner | ⟨hCapture, _⟩
    · exact hxInner hEqInner
    · exact hCapture rfl

end LCS.CutElim.Hauptsatz
end

