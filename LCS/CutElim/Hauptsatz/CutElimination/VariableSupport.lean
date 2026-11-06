import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.NotBound
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

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

/-- A deterministic variable strictly above every index in the finite
proof-wide support and an additional finite avoidance set. -/
noncomputable def freshVariableAvoiding {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (extra : LCS.Finset Nat) : Nat :=
  (LCS.Finset.union T.variableSupport extra).toList.foldl Nat.max 0 + 1

theorem foldl_max_init_le (xs : List Nat) (init : Nat) :
    init ≤ xs.foldl Nat.max init := by
  induction xs generalizing init with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
      exact Nat.le_trans (Nat.le_max_left init x) (ih _)

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
