import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.Trees
import LCS.CutElim.Hauptsatz.CutElimination.VariableSupport
import LCS.CutElim.Hauptsatz.CutElimination.FormulaRenaming
import LCS.CutElim.Hauptsatz.CutElimination.TreeRenaming
import LCS.CutElim.Hauptsatz.CutElimination.Substitution
import LCS.CutElim.Hauptsatz.CutElimination.Hygiene
import LCS.CutElim.Hauptsatz.CutElimination.EigenWeakening
import Attach
import LCS.CutElim.Hauptsatz.CutElimination.Freshening.ProofsStamp

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz
namespace G1nnfProofTree

private noncomputable def freshenEigenvariable {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ)
    (v : Nat) (avoid : LCS.Finset Nat)
    (hv : v ∈ avoid) :
    (∀ w, w ∈ avoid → T.notBoundIn w) →
      EigenFresheningResult T v avoid := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
      intro hBound
      refine
        { tree := G1nnfProofTree.axiom_ rule Γ Δ hAxiom hAC
          depth_eq := rfl
          cutRank_eq := rfl
          notBound_avoid := hBound
          eigen_avoid := ?_ }
      intro w hw hEigen
      exact hEigen.elim
  | onePremise rule Γ Δ hPrem hAC sub ih =>
      intro hBound
      have hSubBound :
          ∀ w, w ∈ avoid → sub.notBoundIn w := by
        intro w hw
        exact
          G1nnfProofTree.notBoundIn_onePremise_subtree
            rule Γ Δ hPrem hAC sub w (hBound w hw)
      let R := ih hSubBound
      by_cases hTarget : ruleEigenlabel rule = some v
      · cases eigenRuleAt_of_target rule v hTarget with
        | allRight x A =>
          exact
            freshenMatchingAllRight
              x v A Γ Δ hPrem hAC sub avoid hv hBound R
        | exLeft x A =>
          exact
            freshenMatchingExLeft
              x v A Γ Δ hPrem hAC sub avoid hv hBound R
      · exact
          EigenFresheningResult.rebuildOne
            rule Γ Δ hPrem hAC sub v avoid hBound R hTarget
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
      intro hBound
      have hSubsBound :
          ∀ w, w ∈ avoid →
            sub1.notBoundIn w ∧ sub2.notBoundIn w := by
        intro w hw
        exact
          G1nnfProofTree.notBoundIn_twoPremise_subtrees
            rule Γ Δ hPrem hAC sub1 sub2 w (hBound w hw)
      let R1 :=
        ih1 (fun w hw => (hSubsBound w hw).1)
      let R2 :=
        ih2 (fun w hw => (hSubsBound w hw).2)
      exact
        EigenFresheningResult.rebuildTwo
          rule Γ Δ hPrem hAC sub1 sub2 v avoid hBound R1 R2
          (no_ruleEigenlabel_of_two_premises
            rule Γ Δ hPrem v) /- ATTACH-BLOCKER: private declaration -/

/-! ### Finite two-phase substitution preparation

The first pass removes every forbidden label from bound positions, including
hidden cut formulae and stored rule data.  The second pass changes only
conflicting eigenlabels.  Both passes keep the indexed root fixed. -/

private theorem termFV_of_mem_termVarIndicesList {L : Language}
    (t : Term L) (v : Nat) :
    v ∈ termVarIndicesList t → termFV t v := by
  induction t with
  | var x =>
      intro hv
      change v = x
      simpa [termVarIndicesList] using hv
  | const c =>
      intro hv
      simpa [termVarIndicesList] using hv
  | func f ts ih =>
      intro hv
      simp only [termVarIndicesList] at hv
      rcases
          (mem_foldl_append_termVariableIndices v ts
            (List.ofFn fun i : Fin (L.funArity f) => i) []).1 hv with
        hEmpty | ⟨i, hi, hvi⟩
      · exact (List.not_mem_nil hEmpty).elim
      · exact ⟨i, ih i hvi⟩ /- ATTACH-BLOCKER: private declaration -/

private theorem mem_termVarIndicesList_of_termFV {L : Language}
    (t : Term L) (v : Nat) (hv : termFV t v) :
    v ∈ termVarIndicesList t := by
  have hSupport := termFV_mem_termVariableSupport t v hv
  simpa only [termVariableSupport, LCS.Finset.mem_ofList] using hSupport /- ATTACH-BLOCKER: private declaration -/

private theorem substitutionTargets_notBound_atRoot {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat)
    (hy : T.notBoundIn y)
    (hFree : freeForAtRoot T t y) :
    ∀ w, w ∈ y :: termVarIndicesList t →
      (∀ A ∈ Γ, FormulaN.notBoundIn w A) ∧
      (∀ A ∈ Δ, FormulaN.notBoundIn w A) := by
  intro w hw
  rcases List.mem_cons.mp hw with hwy | hw
  · subst w
    exact T.notBoundIn_atRoot y hy
  · have hwFV : termFV t w :=
      termFV_of_mem_termVarIndicesList t w hw
    have hyRoot := T.notBoundIn_atRoot y hy
    constructor
    · intro A hA
      exact
        FormulaN.notBoundIn_and_freeFor_termFV_not_bound
          A t y w (hyRoot.1 A hA) (hFree.1 A hA) hwFV
    · intro A hA
      exact
        FormulaN.notBoundIn_and_freeFor_termFV_not_bound
          A t y w (hyRoot.2 A hA) (hFree.2 A hA) hwFV /- ATTACH-BLOCKER: private declaration -/

private structure BoundHygieneResult {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (targets : List Nat) where
  tree : G1nnfProofTree hL Γ Δ
  depth_eq : tree.depth = T.depth
  cutRank_eq : tree.cutRank = T.cutRank
  eigenvariables_eq :
    ∀ w, tree.eigenvariables w = T.eigenvariables w
  notBound_targets :
    ∀ w, w ∈ targets → tree.notBoundIn w /- ATTACH-BLOCKER: private declaration -/

private noncomputable def hygienizeBoundVariables {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (targets : List Nat)
    (hRoot :
      ∀ w, w ∈ targets →
        (∀ A ∈ Γ, FormulaN.notBoundIn w A) ∧
        (∀ A ∈ Δ, FormulaN.notBoundIn w A)) :
    BoundHygieneResult T targets := by
  induction targets generalizing T with
  | nil =>
      refine
        { tree := T
          depth_eq := rfl
          cutRank_eq := rfl
          eigenvariables_eq := fun _ => rfl
          notBound_targets := ?_ }
      intro w hw
      exact (List.not_mem_nil hw).elim
  | cons v targets ih =>
      have hTailRoot :
          ∀ w, w ∈ targets →
            (∀ A ∈ Γ, FormulaN.notBoundIn w A) ∧
            (∀ A ∈ Δ, FormulaN.notBoundIn w A) := by
        intro w hw
        exact hRoot w (List.mem_cons.mpr (Or.inr hw))
      let R := ih T hTailRoot
      let extra := LCS.Finset.ofList (v :: targets)
      let z := R.tree.freshVariableAvoiding extra
      have hzTree : z ∉ R.tree.variableSupport := by
        simpa only [z] using
          R.tree.freshVariableAvoiding_not_mem_variableSupport extra
      have hzExtra : z ∉ extra := by
        simpa only [z] using
          R.tree.freshVariableAvoiding_not_mem_extra extra
      have hvz : v ≠ z := by
        intro hvz
        have hvMem : v ∈ extra := by
          simpa only [extra, LCS.Finset.mem_ofList] using
            (List.mem_cons.mpr (Or.inl rfl) :
              v ∈ v :: targets)
        exact hzExtra (hvz ▸ hvMem)
      have hRootV :
          (∀ A ∈ Γ, FormulaN.notBoundIn v A) ∧
          (∀ A ∈ Δ, FormulaN.notBoundIn v A) :=
        hRoot v (List.mem_cons.mpr (Or.inl rfl))
      let T' :=
        R.tree.alphaRenameBoundAtRoot
          v z hvz hzTree hRootV
      refine
        { tree := T'
          depth_eq := ?_
          cutRank_eq := ?_
          eigenvariables_eq := ?_
          notBound_targets := ?_ }
      · calc
          T'.depth = R.tree.depth := by
            simpa only [T'] using
              R.tree.alphaRenameBoundAtRoot_depth
                v z hvz hzTree hRootV
          _ = T.depth := R.depth_eq
      · calc
          T'.cutRank = R.tree.cutRank := by
            simpa only [T'] using
              R.tree.alphaRenameBoundAtRoot_cutRank
                v z hvz hzTree hRootV
          _ = T.cutRank := R.cutRank_eq
      · intro w
        calc
          T'.eigenvariables w = R.tree.eigenvariables w := by
            simpa only [T'] using
              R.tree.alphaRenameBoundAtRoot_eigenvariables_eq
                v z hvz hzTree hRootV w
          _ = T.eigenvariables w := R.eigenvariables_eq w
      · intro w hw
        rcases List.mem_cons.mp hw with hwv | hwTail
        · subst w
          simpa only [T'] using
            R.tree.alphaRenameBoundAtRoot_notBound_target
              v z hvz hzTree hRootV
        · have hwz : w ≠ z := by
            intro hwz
            have hwMem : w ∈ extra := by
              simpa only [extra, LCS.Finset.mem_ofList] using
                (List.mem_cons.mpr (Or.inr hwTail) :
                  w ∈ v :: targets)
            exact hzExtra (hwz ▸ hwMem)
          simpa only [T'] using
            R.tree.alphaRenameBoundAtRoot_preserves_notBound
              v z w hvz hzTree hRootV hwz
                (R.notBound_targets w hwTail) /- ATTACH-BLOCKER: private declaration -/

private structure EigenHygieneResult {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (targets : List Nat)
    (avoid : LCS.Finset Nat) where
  tree : G1nnfProofTree hL Γ Δ
  depth_eq : tree.depth = T.depth
  cutRank_eq : tree.cutRank = T.cutRank
  notBound_avoid :
    ∀ w, w ∈ avoid → tree.notBoundIn w
  notEigen_targets :
    ∀ w, w ∈ targets → ¬ tree.eigenvariables w
  eigenvariables_from_original :
    ∀ w, w ∈ avoid → tree.eigenvariables w →
      T.eigenvariables w /- ATTACH-BLOCKER: private declaration -/

private noncomputable def hygienizeEigenvariables {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (targets : List Nat)
    (avoid : LCS.Finset Nat)
    (hTargets : ∀ w, w ∈ targets → w ∈ avoid)
    (hBound : ∀ w, w ∈ avoid → T.notBoundIn w) :
    EigenHygieneResult T targets avoid := by
  induction targets generalizing T with
  | nil =>
      refine
        { tree := T
          depth_eq := rfl
          cutRank_eq := rfl
          notBound_avoid := hBound
          notEigen_targets := ?_
          eigenvariables_from_original := ?_ }
      · intro w hw
        exact (List.not_mem_nil hw).elim
      · intro w hw hEigen
        exact hEigen
  | cons v targets ih =>
      have hv : v ∈ avoid :=
        hTargets v (List.mem_cons.mpr (Or.inl rfl))
      let R := T.freshenEigenvariable v avoid hv hBound
      have hTailTargets :
          ∀ w, w ∈ targets → w ∈ avoid := by
        intro w hw
        exact hTargets w (List.mem_cons.mpr (Or.inr hw))
      let Q :=
        ih R.tree hTailTargets R.notBound_avoid
      refine
        { tree := Q.tree
          depth_eq := ?_
          cutRank_eq := ?_
          notBound_avoid := Q.notBound_avoid
          notEigen_targets := ?_
          eigenvariables_from_original := ?_ }
      · exact Q.depth_eq.trans R.depth_eq
      · exact Q.cutRank_eq.trans R.cutRank_eq
      · intro w hw
        rcases List.mem_cons.mp hw with hwv | hwTail
        · intro hEigen
          have hR :
              R.tree.eigenvariables w :=
            Q.eigenvariables_from_original w
              (hTargets w
                (List.mem_cons.mpr (Or.inl hwv))) hEigen
          subst w
          exact R.notEigen_target hv hR
        · exact Q.notEigen_targets w hwTail
      · intro w hw hEigen
        have hR :
            R.tree.eigenvariables w :=
          Q.eigenvariables_from_original w hw hEigen
        exact (R.eigen_avoid w hw hR).2 /- ATTACH-BLOCKER: private declaration -/

structure SubstitutionPreparation {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat) where
  tree : G1nnfProofTree hL Γ Δ
  depth_eq : tree.depth = T.depth
  cutRank_eq : tree.cutRank = T.cutRank
  treeSubstOk : tree.treeSubstOk t y

/-- Internal realization of Gallier's root-only substitution hypotheses.
The returned tree has the same indexed conclusion, depth, and cut rank, but
its hidden binders and eigenlabels have been made safe for direct
substitution. -/
noncomputable def prepareSubstitution {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (t : Term L) (y : Nat)
    (hy : T.notBoundIn y)
    (hFree : freeForAtRoot T t y) :
    SubstitutionPreparation T t y := by
  let targets := y :: termVarIndicesList t
  let avoid := LCS.Finset.ofList targets
  have hRoot :
      ∀ w, w ∈ targets →
        (∀ A ∈ Γ, FormulaN.notBoundIn w A) ∧
        (∀ A ∈ Δ, FormulaN.notBoundIn w A) := by
    intro w hw
    apply substitutionTargets_notBound_atRoot T t y hy hFree
    simpa only [targets] using hw
  let B := hygienizeBoundVariables T targets hRoot
  have hTargetsAvoid :
      ∀ w, w ∈ targets → w ∈ avoid := by
    intro w hw
    simpa only [avoid, LCS.Finset.mem_ofList] using hw
  have hBound :
      ∀ w, w ∈ avoid → B.tree.notBoundIn w := by
    intro w hw
    apply B.notBound_targets w
    simpa only [avoid, LCS.Finset.mem_ofList] using hw
  let E :=
    hygienizeEigenvariables
      B.tree targets avoid hTargetsAvoid hBound
  have hyTarget : y ∈ targets := by
    simp [targets]
  have hyAvoid : y ∈ avoid :=
    hTargetsAvoid y hyTarget
  have hyBound : E.tree.notBoundIn y :=
    E.notBound_avoid y hyAvoid
  have htBound :
      ∀ w, termFV t w → E.tree.notBoundIn w := by
    intro w hw
    have hwTarget : w ∈ targets := by
      simp only [targets, List.mem_cons]
      exact Or.inr (mem_termVarIndicesList_of_termFV t w hw)
    exact E.notBound_avoid w (hTargetsAvoid w hwTarget)
  have hyEigen : ¬ E.tree.eigenvariables y :=
    E.notEigen_targets y hyTarget
  have htEigen :
      ∀ w, termFV t w → ¬ E.tree.eigenvariables w := by
    intro w hw
    have hwTarget : w ∈ targets := by
      simp only [targets, List.mem_cons]
      exact Or.inr (mem_termVarIndicesList_of_termFV t w hw)
    exact E.notEigen_targets w hwTarget
  refine
    { tree := E.tree
      depth_eq := ?_
      cutRank_eq := ?_
      treeSubstOk :=
        treeSubstOk_of_hygiene
          E.tree t y hyBound htBound hyEigen htEigen }
  · exact E.depth_eq.trans B.depth_eq
  · exact E.cutRank_eq.trans B.cutRank_eq

private noncomputable def positiveAtomicIdentityIn {L : Language} {hL : L.withoutEquality}
    (A : FormulaN L) (hAtom : A.isAtomic = true)
    (hANNF : A.isNNF)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ))
    (hAΓ : A ∈ Γ) (hAΔ : A ∈ Δ) :
    G1nnfProofTree hL Γ Δ := by
  let core :=
    G1nnfProofTree.axiom_ (hL := hL)
      (.axiomPosAtomic A hAtom Γ Δ) Γ Δ rfl
      ⟨trivial,
        G1nnfFinsetSequent.IsNNF.insert_right hANNF
          (G1nnfFinsetSequent.IsNNF.insert_left hANNF hNNF)⟩
  exact
    core.castTree
      (finset_insert_eq_self_of_mem hAΓ)
      (finset_insert_eq_self_of_mem hAΔ) /- ATTACH-BLOCKER: private declaration -/

private theorem positiveAtomicIdentityIn_allFormulae {L : Language} {hL : L.withoutEquality}
    (A : FormulaN L) (hAtom : A.isAtomic = true)
    (hANNF : A.isNNF)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ))
    (hAΓ : A ∈ Γ) (hAΔ : A ∈ Δ) :
    (positiveAtomicIdentityIn (hL := hL)
      A hAtom hANNF Γ Δ hNNF hAΓ hAΔ).allFormulae =
        LCS.Finset.union Γ Δ := by
  unfold positiveAtomicIdentityIn
  refine (allFormulae_cast _ _ _).trans ?_
  simp only [G1nnfProofTree.allFormulae, G1nnfRule.conclusion]
  rw [finset_insert_eq_self_of_mem hAΓ,
    finset_insert_eq_self_of_mem hAΔ] /- ATTACH-BLOCKER: private declaration -/

private theorem positiveAtomicIdentityIn_notBound {L : Language} {hL : L.withoutEquality}
    (A : FormulaN L) (hAtom : A.isAtomic = true)
    (hANNF : A.isNNF)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ))
    (hAΓ : A ∈ Γ) (hAΔ : A ∈ Δ)
    (y : Nat) (hΓ : ∀ F ∈ Γ, FormulaN.notBoundIn y F)
    (hΔ : ∀ F ∈ Δ, FormulaN.notBoundIn y F) :
    (positiveAtomicIdentityIn (hL := hL)
      A hAtom hANNF Γ Δ hNNF hAΓ hAΔ).notBoundIn y := by
  intro F hF
  rw [positiveAtomicIdentityIn_allFormulae
    A hAtom hANNF Γ Δ hNNF hAΓ hAΔ] at hF
  rcases LCS.Finset.mem_union.mp hF with hF | hF
  · exact hΓ F hF
  · exact hΔ F hF /- ATTACH-BLOCKER: private declaration -/

private theorem notBoundIn_onePremise_of_parts {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 1)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (y : Nat)
    (hLeft :
      ∀ F ∈ (rule.conclusion Γ Δ).1,
        FormulaN.notBoundIn y F)
    (hRight :
      ∀ F ∈ (rule.conclusion Γ Δ).2,
        FormulaN.notBoundIn y F)
    (hSub : sub.notBoundIn y) :
    (G1nnfProofTree.onePremise
      rule Γ Δ hPrem hAC sub).notBoundIn y := by
  intro F hF
  simp only [G1nnfProofTree.allFormulae] at hF
  rcases LCS.Finset.mem_union.mp hF with hRoot | hSubtree
  · rcases LCS.Finset.mem_union.mp hRoot with hF | hF
    · exact hLeft F hF
    · exact hRight F hF
  · exact hSub F hSubtree /- ATTACH-BLOCKER: private declaration -/

private theorem notBoundIn_twoPremise_of_parts {L : Language} {hL : L.withoutEquality}
    (rule : G1nnfRule L)
    (Γ Δ : LCS.Finset (FormulaN L))
    (hPrem : (rule.premises Γ Δ).length = 2)
    (hAC : rule.ApplicationConditions Γ Δ)
    (sub1 : G1nnfProofTree hL
      ((rule.premises Γ Δ)[0]'(by omega)).1
      ((rule.premises Γ Δ)[0]'(by omega)).2)
    (sub2 : G1nnfProofTree hL
      ((rule.premises Γ Δ)[1]'(by omega)).1
      ((rule.premises Γ Δ)[1]'(by omega)).2)
    (y : Nat)
    (hLeft :
      ∀ F ∈ (rule.conclusion Γ Δ).1,
        FormulaN.notBoundIn y F)
    (hRight :
      ∀ F ∈ (rule.conclusion Γ Δ).2,
        FormulaN.notBoundIn y F)
    (hSub1 : sub1.notBoundIn y)
    (hSub2 : sub2.notBoundIn y) :
    (G1nnfProofTree.twoPremise
      rule Γ Δ hPrem hAC sub1 sub2).notBoundIn y := by
  intro F hF
  simp only [G1nnfProofTree.allFormulae] at hF
  rcases LCS.Finset.mem_union.mp hF with hRoot | hSubtrees
  · rcases LCS.Finset.mem_union.mp hRoot with hF | hF
    · exact hLeft F hF
    · exact hRight F hF
  · rcases LCS.Finset.mem_union.mp hSubtrees with hF | hF
    · exact hSub1 F hF
    · exact hSub2 F hF /- ATTACH-BLOCKER: private declaration -/

private def hiddenCutSubstitutionAtom : FormulaN nnfExLang :=
  .predN NnfExPred.P (nnfVec1 1) /- ATTACH-BLOCKER: private declaration -/

private def hiddenCutSubstitutionFormula : FormulaN nnfExLang :=
  .all 0 hiddenCutSubstitutionAtom /- ATTACH-BLOCKER: private declaration -/

private def hiddenCutSubstitutionRoot :
    LCS.Finset (FormulaN nnfExLang) :=
  LCS.Finset.singleton hiddenCutSubstitutionAtom /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionAtom_isNNF :
    hiddenCutSubstitutionAtom.isNNF := by
  trivial /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionFormula_isNNF :
    hiddenCutSubstitutionFormula.isNNF :=
  hiddenCutSubstitutionAtom_isNNF /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionAtom_mem_root :
    hiddenCutSubstitutionAtom ∈ hiddenCutSubstitutionRoot :=
  (LCS.Finset.mem_singleton
    hiddenCutSubstitutionAtom hiddenCutSubstitutionAtom).2 rfl /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionRoot_isNNF :
    G1nnfFinsetSequent.IsNNF
      (hiddenCutSubstitutionRoot, hiddenCutSubstitutionRoot) := by
  constructor <;> intro F hF
  all_goals
    have hEq :=
      (LCS.Finset.mem_singleton
        F hiddenCutSubstitutionAtom).1 hF
    subst F
    exact hiddenCutSubstitutionAtom_isNNF /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionTargetFreshAtom :
    0 ∉ formulaFVN hiddenCutSubstitutionAtom := by
  intro h
  change ∃ i : Fin 1, termFV (nnfVec1 1 i) 0 at h
  rcases h with ⟨i, hi⟩
  rcases i with ⟨i, hiBound⟩
  have hi0 : i = 0 := by omega
  subst i
  change 0 = 1 at hi
  omega /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionInstance_eq :
    formulaSubstN hiddenCutSubstitutionAtom (.var 2) 0 =
      hiddenCutSubstitutionAtom := by
  exact formulaSubstN_eq_self_of_not_free
    hiddenCutSubstitutionAtom (.var 2) 0
    hiddenCutSubstitutionTargetFreshAtom /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionAtom_notBound :
    FormulaN.notBoundIn 1 hiddenCutSubstitutionAtom := by
  intro h
  exact h.elim /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionFormula_notBound :
    FormulaN.notBoundIn 1 hiddenCutSubstitutionFormula := by
  change ¬ (formulaBVN hiddenCutSubstitutionAtom 1 ∨ 1 = 0)
  intro h
  rcases h with h | h
  · exact hiddenCutSubstitutionAtom_notBound h
  · omega /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionRoot_notBound :
    ∀ F ∈ hiddenCutSubstitutionRoot,
      FormulaN.notBoundIn 1 F := by
  intro F hF
  have hEq :=
    (LCS.Finset.mem_singleton
      F hiddenCutSubstitutionAtom).1 hF
  subst F
  exact hiddenCutSubstitutionAtom_notBound /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionFreshAtom :
    2 ∉ formulaFVN hiddenCutSubstitutionAtom := by
  intro h
  change ∃ i : Fin 1, termFV (nnfVec1 1 i) 2 at h
  rcases h with ⟨i, hi⟩
  rcases i with ⟨i, hiBound⟩
  have hi0 : i = 0 := by omega
  subst i
  change 2 = 1 at hi
  omega /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionFreshFormula :
    2 ∉ formulaFVN hiddenCutSubstitutionFormula := by
  intro h
  exact hiddenCutSubstitutionFreshAtom h.1 /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionFreshRoot :
    ∀ F ∈ hiddenCutSubstitutionRoot,
      2 ∉ formulaFVN F := by
  intro F hF
  have hEq :=
    (LCS.Finset.mem_singleton
      F hiddenCutSubstitutionAtom).1 hF
  subst F
  exact hiddenCutSubstitutionFreshAtom /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionPremise_isNNF :
    G1nnfFinsetSequent.IsNNF
      (hiddenCutSubstitutionRoot,
        LCS.Finset.insert
          (formulaSubstN hiddenCutSubstitutionAtom (.var 2) 0)
          hiddenCutSubstitutionRoot) :=
  G1nnfFinsetSequent.IsNNF.insert_right
    (isNNF_formulaSubstN
      hiddenCutSubstitutionAtom (.var 2) 0
      hiddenCutSubstitutionAtom_isNNF)
    hiddenCutSubstitutionRoot_isNNF /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionAtom_mem_premise :
    hiddenCutSubstitutionAtom ∈
      LCS.Finset.insert
        (formulaSubstN hiddenCutSubstitutionAtom (.var 2) 0)
        hiddenCutSubstitutionRoot :=
  LCS.Finset.mem_insert.mpr
    (Or.inr hiddenCutSubstitutionAtom_mem_root) /- ATTACH-BLOCKER: private declaration -/

private noncomputable def hiddenCutSubstitutionAllPremise :
    G1nnfProofTree nnfExLang_withoutEquality hiddenCutSubstitutionRoot
      (LCS.Finset.insert
        (formulaSubstN hiddenCutSubstitutionAtom (.var 2) 0)
        hiddenCutSubstitutionRoot) :=
  positiveAtomicIdentityIn
    hiddenCutSubstitutionAtom rfl
    hiddenCutSubstitutionAtom_isNNF
    hiddenCutSubstitutionRoot
    (LCS.Finset.insert
      (formulaSubstN hiddenCutSubstitutionAtom (.var 2) 0)
      hiddenCutSubstitutionRoot)
    hiddenCutSubstitutionPremise_isNNF
    hiddenCutSubstitutionAtom_mem_root
    hiddenCutSubstitutionAtom_mem_premise /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionAllPremise_notBound :
    hiddenCutSubstitutionAllPremise.notBoundIn 1 := by
  apply positiveAtomicIdentityIn_notBound
  · exact hiddenCutSubstitutionRoot_notBound
  · intro F hF
    rcases LCS.Finset.mem_insert.mp hF with hF | hF
    · rw [hiddenCutSubstitutionInstance_eq] at hF
      subst F
      exact hiddenCutSubstitutionAtom_notBound
    · exact hiddenCutSubstitutionRoot_notBound F hF /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionAllRight_conditions :
    (G1nnfRule.allRight
      0 hiddenCutSubstitutionAtom 2).ApplicationConditions
        hiddenCutSubstitutionRoot hiddenCutSubstitutionRoot :=
  ⟨G1nnfRule.sideConditions_allRight_of_fresh
      0 2 hiddenCutSubstitutionAtom
      hiddenCutSubstitutionRoot hiddenCutSubstitutionRoot
      trivial hiddenCutSubstitutionFreshFormula
      hiddenCutSubstitutionFreshRoot
      hiddenCutSubstitutionFreshRoot,
    G1nnfFinsetSequent.IsNNF.insert_right
      hiddenCutSubstitutionFormula_isNNF
      hiddenCutSubstitutionRoot_isNNF⟩ /- ATTACH-BLOCKER: private declaration -/

private noncomputable def hiddenCutSubstitutionLeftSubtree :
    G1nnfProofTree nnfExLang_withoutEquality hiddenCutSubstitutionRoot
      (LCS.Finset.insert hiddenCutSubstitutionFormula
        hiddenCutSubstitutionRoot) :=
  G1nnfProofTree.onePremise
    (.allRight 0 hiddenCutSubstitutionAtom 2)
    hiddenCutSubstitutionRoot hiddenCutSubstitutionRoot
    rfl hiddenCutSubstitutionAllRight_conditions
    hiddenCutSubstitutionAllPremise /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionLeftSubtree_notBound :
    hiddenCutSubstitutionLeftSubtree.notBoundIn 1 := by
  apply notBoundIn_onePremise_of_parts
  · exact hiddenCutSubstitutionRoot_notBound
  · intro F hF
    rcases LCS.Finset.mem_insert.mp hF with hF | hF
    · subst F
      exact hiddenCutSubstitutionFormula_notBound
    · exact hiddenCutSubstitutionRoot_notBound F hF
  · exact hiddenCutSubstitutionAllPremise_notBound /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionLeftPremise_isNNF :
    G1nnfFinsetSequent.IsNNF
      (LCS.Finset.insert hiddenCutSubstitutionFormula
        hiddenCutSubstitutionRoot,
        hiddenCutSubstitutionRoot) :=
  G1nnfFinsetSequent.IsNNF.insert_left
    hiddenCutSubstitutionFormula_isNNF
    hiddenCutSubstitutionRoot_isNNF /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionAtom_mem_left :
    hiddenCutSubstitutionAtom ∈
      LCS.Finset.insert hiddenCutSubstitutionFormula
        hiddenCutSubstitutionRoot :=
  LCS.Finset.mem_insert.mpr
    (Or.inr hiddenCutSubstitutionAtom_mem_root) /- ATTACH-BLOCKER: private declaration -/

private noncomputable def hiddenCutSubstitutionRightSubtree :
    G1nnfProofTree nnfExLang_withoutEquality
      (LCS.Finset.insert hiddenCutSubstitutionFormula
        hiddenCutSubstitutionRoot)
      hiddenCutSubstitutionRoot :=
  positiveAtomicIdentityIn
    hiddenCutSubstitutionAtom rfl
    hiddenCutSubstitutionAtom_isNNF
    (LCS.Finset.insert hiddenCutSubstitutionFormula
      hiddenCutSubstitutionRoot)
    hiddenCutSubstitutionRoot
    hiddenCutSubstitutionLeftPremise_isNNF
    hiddenCutSubstitutionAtom_mem_left
    hiddenCutSubstitutionAtom_mem_root /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionRightSubtree_notBound :
    hiddenCutSubstitutionRightSubtree.notBoundIn 1 := by
  apply positiveAtomicIdentityIn_notBound
  · intro F hF
    rcases LCS.Finset.mem_insert.mp hF with hF | hF
    · subst F
      exact hiddenCutSubstitutionFormula_notBound
    · exact hiddenCutSubstitutionRoot_notBound F hF
  · exact hiddenCutSubstitutionRoot_notBound /- ATTACH-BLOCKER: private declaration -/

/-- The adversarial derivation behind the preparation contract.  Its endpoint
is the atomic identity `P(y) ⇒ P(y)`, but it contains the hidden cut
`∀x P(y)` and introduces that cut formula by a legal universal-right step. -/
private noncomputable def hiddenCutSubstitutionTree :
    G1nnfProofTree nnfExLang_withoutEquality hiddenCutSubstitutionRoot
      hiddenCutSubstitutionRoot := by
  have hConc := G1nnfRule.cut_shared_conclusion hiddenCutSubstitutionFormula
    hiddenCutSubstitutionRoot hiddenCutSubstitutionRoot
  have hAC : G1nnfRule.ApplicationConditions
      (.cut hiddenCutSubstitutionFormula
        hiddenCutSubstitutionRoot hiddenCutSubstitutionRoot)
      hiddenCutSubstitutionRoot hiddenCutSubstitutionRoot := by
    refine ⟨trivial, ?_⟩
    simpa only [hConc] using hiddenCutSubstitutionRoot_isNNF
  let tree := G1nnfProofTree.twoPremise
    (.cut hiddenCutSubstitutionFormula
      hiddenCutSubstitutionRoot hiddenCutSubstitutionRoot)
    hiddenCutSubstitutionRoot hiddenCutSubstitutionRoot rfl hAC
    hiddenCutSubstitutionLeftSubtree hiddenCutSubstitutionRightSubtree
  exact tree.castTree (congrArg Prod.fst hConc) (congrArg Prod.snd hConc) /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionTree_notBound :
    hiddenCutSubstitutionTree.notBoundIn 1 := by
  unfold hiddenCutSubstitutionTree
  apply (notBoundIn_cast _ _ _ _).2
  apply notBoundIn_twoPremise_of_parts
  · simpa only [G1nnfRule.cut_shared_conclusion] using
      hiddenCutSubstitutionRoot_notBound
  · simpa only [G1nnfRule.cut_shared_conclusion] using
      hiddenCutSubstitutionRoot_notBound
  · exact hiddenCutSubstitutionLeftSubtree_notBound
  · exact hiddenCutSubstitutionRightSubtree_notBound /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionTree_freeForAtRoot :
    freeForAtRoot hiddenCutSubstitutionTree (.var 0) 1 := by
  constructor <;> intro F hF
  all_goals
    have hEq :=
      (LCS.Finset.mem_singleton
        F hiddenCutSubstitutionAtom).1 hF
    subst F
    trivial /- ATTACH-BLOCKER: private declaration -/

private theorem hiddenCutSubstitutionTree_direct_rejected :
    ¬ hiddenCutSubstitutionTree.treeSubstOk (.var 0) 1 := by
  have hCast {Γ Δ Γ' Δ' : LCS.Finset (FormulaN nnfExLang)}
      (T : G1nnfProofTree nnfExLang_withoutEquality Γ Δ)
      (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
      (T.castTree hΓ hΔ).treeSubstOk (.var 0) 1 =
        T.treeSubstOk (.var 0) 1 := by
    subst Γ'
    subst Δ'
    rfl
  intro hOk
  simp only [hiddenCutSubstitutionTree, hCast,
    hiddenCutSubstitutionLeftSubtree,
    G1nnfProofTree.treeSubstOk, ruleSubstOk] at hOk
  exact hOk.2.1.1.2.1 rfl /- ATTACH-BLOCKER: private declaration -/

/-- Adversarial preparation regression: direct substitution into the hidden
cut derivation is rejected because `x ∈ FV(var x)`, while the two-phase
preparation produces an exact-root tree with the same depth and cut rank
whose internal substitution contract is inhabited. -/
theorem prepareSubstitution_hiddenCut_regression :
    (¬ hiddenCutSubstitutionTree.treeSubstOk (.var 0) 1) ∧
    ∃ T' :
        G1nnfProofTree nnfExLang_withoutEquality hiddenCutSubstitutionRoot
          hiddenCutSubstitutionRoot,
      T'.depth = hiddenCutSubstitutionTree.depth ∧
      T'.cutRank = hiddenCutSubstitutionTree.cutRank ∧
      T'.treeSubstOk (.var 0) 1 := by
  refine ⟨hiddenCutSubstitutionTree_direct_rejected, ?_⟩
  let R :=
    hiddenCutSubstitutionTree.prepareSubstitution
      (.var 0) 1 hiddenCutSubstitutionTree_notBound
      hiddenCutSubstitutionTree_freeForAtRoot
  exact ⟨R.tree, R.depth_eq, R.cutRank_eq, R.treeSubstOk⟩ /- ATTACH-BLOCKER: private name in relocated declaration -/

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

/-- Internal substitution lemma under the direct rule-admissibility contract. -/
theorem g1nnf_substitution_of_treeSubstOk {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y : Nat) (t : Term L)
    (hOk : T.treeSubstOk t y) :
    ∃ T' : G1nnfProofTree hL (substFormulaFinset Γ t y) (substFormulaFinset Δ t y),
      T'.depth = T.depth
      ∧ T'.cutRank = T.cutRank
      ∧ (¬ T'.eigenvariables y)
      ∧ (∀ v, termFV t v → ¬ T'.eigenvariables v)
      ∧ T'.conclusion = (substFormulaFinset Γ t y, substFormulaFinset Δ t y) := by
-- BEGIN PROOF
  have hDisjoint := T.treeSubstOk_eigenvariables_disjoint y t hOk
  refine ⟨T.substTerm t y hOk, T.substTerm_depth y t hOk,
    T.substTerm_cutRank y t hOk, ?_, ?_, rfl⟩
  · rw [T.substTerm_eigenvariables_eq y t hOk y]
    exact hDisjoint.1
  · intro v hv
    rw [T.substTerm_eigenvariables_eq y t hOk v]
    exact hDisjoint.2 v hv /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

/-- Lemma 6.4.4 (Substitution lemma): if `y` is not bound in T and
`t` is free for `y` in its root sequent, there is a proof of the substituted
sequent with the same depth and cut rank. Neither `y` nor any variable of
`t` is an eigenvariable of the resulting proof. -/
@[blueprint "chap6__lemma_6_4_4" (main := true)]
theorem g1nnf_substitution_lemma {L : Language}
    {hL : L.withoutEquality} {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G1nnfProofTree hL Γ Δ) (y : Nat) (t : Term L)
    (hNotBound : T.notBoundIn y) (hFree : freeForAtRoot T t y) :
    ∃ T' : G1nnfProofTree hL (substFormulaFinset Γ t y) (substFormulaFinset Δ t y),
      T'.depth = T.depth ∧ T'.cutRank = T.cutRank ∧
      (¬ T'.eigenvariables y) ∧
      (∀ v, termFV t v → ¬ T'.eigenvariables v) ∧
      T'.conclusion = (substFormulaFinset Γ t y, substFormulaFinset Δ t y)

-- ===================================================================
-- Theorem 6.4.1 (companion): iterExp
-- ===================================================================

/-- Theorem 6.4.1 (required helper): Iterated exponentiation,
`iterExp m n p = m ^ (m ^ ... ^ p)` with `n` base-`m` exponentiations.
Used to state the depth bound of the cut-elimination procedure
`g1nnf_cut_eliminate`: `depth(T*) ≤ exp(2, c(T), depth(T))`. -/
@[blueprint "chap6__theorem_6_4_1"]
def iterExp : Nat → Nat → Nat → Nat
  | _, 0, p => p
  | m, n + 1, p => m ^ iterExp m n p

-- ===================================================================
-- Section D: Degree helpers
-- ===================================================================













-- ===================================================================
-- Section E: iterExp helpers
-- ===================================================================

theorem iterExp_mono_last (m : Nat) (hm : 1 ≤ m) :
    ∀ (n : Nat), ∀ {p q : Nat}, p ≤ q → iterExp m n p ≤ iterExp m n q := by
-- BEGIN PROOF
  intro n
  induction n with
  | zero => intro p q hpq; simp [iterExp]; exact hpq
  | succ n ih =>
    intro p q hpq
    simp only [iterExp]
    exact Nat.pow_le_pow_right (by omega) (ih hpq) /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

theorem nat_le_pow_of_two_le (b n : Nat) (hb : 2 ≤ b) : n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hPow : 1 ≤ b ^ n := Nat.one_le_pow n b (by omega)
    calc
      n + 1 ≤ b ^ n + 1 := by omega
      _ ≤ b ^ n + b ^ n := by omega
      _ = 2 * b ^ n := by omega
      _ ≤ b * b ^ n := Nat.mul_le_mul_right (b ^ n) hb
      _ = b ^ (n + 1) := by simp [Nat.pow_succ, Nat.mul_comm] /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/



theorem iterExp_mono_count_of_two_le (b : Nat) (hb : 2 ≤ b) :
    ∀ (n₁ n₂ p : Nat), n₁ ≤ n₂ → iterExp b n₁ p ≤ iterExp b n₂ p := by
-- BEGIN PROOF
  intro n₁ n₂ p hn
  induction n₂ with
  | zero =>
    have : n₁ = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ n₂ ih =>
    by_cases h : n₁ ≤ n₂
    · calc iterExp b n₁ p ≤ iterExp b n₂ p := ih h
      _ ≤ b ^ iterExp b n₂ p :=
        nat_le_pow_of_two_le b (iterExp b n₂ p) hb
      _ = iterExp b (n₂ + 1) p := by simp [iterExp]
    · have : n₁ = n₂ + 1 := by omega
      subst this; exact Nat.le_refl _ /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

theorem iterExp_mono_count :
    ∀ (n₁ n₂ p : Nat), n₁ ≤ n₂ → iterExp 2 n₁ p ≤ iterExp 2 n₂ p := by
-- BEGIN PROOF
  intro n₁ n₂ p hn
  exact iterExp_mono_count_of_two_le 2 (by omega) n₁ n₂ p hn /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

theorem iterExp_succ_shift_base :
    ∀ (b n p : Nat), iterExp b (n + 1) p = iterExp b n (b ^ p) := by
-- BEGIN PROOF
  intro b n
  induction n with
  | zero => intro p; simp [iterExp]
  | succ n ih =>
    intro p
    show b ^ iterExp b (n + 1) p = b ^ iterExp b n (b ^ p)
    congr 1
    exact ih p /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

theorem iterExp_succ_shift :
    ∀ (n p : Nat), iterExp 2 (n + 1) p = iterExp 2 n (2 ^ p) := by
-- BEGIN PROOF
  intro n p
  exact iterExp_succ_shift_base 2 n p /- retained: used by LCS.CutElim.Hauptsatz.CutElimination.SubstitutionRegression.Proofs -/

theorem G1nnfProofTree.depth_mpr_left {L : Language} {hL : L.withoutEquality}
    {Γ Γ' Δ : LCS.Finset (FormulaN L)}
    (hidx : Γ = Γ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ' Δ)
    (T : G1nnfProofTree hL Γ' Δ) :
    (@G1nnfProofTree.depth L hL Γ Δ
      (@Eq.mpr (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ' Δ) htype T)) =
      (@G1nnfProofTree.depth L hL Γ' Δ T) := by
  subst Γ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.depth_mp {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ' Δ')
    (T : G1nnfProofTree hL Γ Δ) :
    (@G1nnfProofTree.depth L hL Γ' Δ'
      (@Eq.mp (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ' Δ') htype T)) =
      (@G1nnfProofTree.depth L hL Γ Δ T) := by
  subst Γ'
  subst Δ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem nat_max_congr {a b c d : Nat} (h₁ : a = b) (h₂ : c = d) :
    max a c = max b d := by
  cases h₁
  cases h₂
  rfl /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

theorem G1nnfProofTree.weakenTreeLeft_depth {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v) :
    (T.weakenTreeLeft A hNNF hFV).depth = T.depth := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    simp only [G1nnfProofTree.weakenTreeLeft]
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_left
        rule Γ Δ A hAxiom hAC hNNF
    have hSpec := Classical.choose_spec hWeakened
    have hGamma :
        ((Classical.choose hWeakened).conclusion Γ Δ).1 =
          LCS.Finset.insert A (rule.conclusion Γ Δ).1 := by
      simpa using congrArg Prod.fst hSpec.2.2
    have hDelta :
        ((Classical.choose hWeakened).conclusion Γ Δ).2 =
          (rule.conclusion Γ Δ).2 := by
      simpa using congrArg Prod.snd hSpec.2.2
    rw [G1nnfProofTree.depth_mp hGamma hDelta]
    rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    cases rule with
    | conjLeft1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm A (.conj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm B A Γ) _ _).trans (ih _)
    | conjLeft2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm A (.conj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm C A Γ) _ _).trans (ih _)
    | disjRight1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | disjRight2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | allLeft x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm A (.all x B) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm (formulaSubstN B t x) A Γ) _ _).trans
        (ih _)
    | allRight x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | exLeft x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm A (.ex x B) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm
          (formulaSubstN B (.var y) x) A Γ) _ _).trans (ih _)
    | exRight x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    cases rule with
    | cut B Lam Theta =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_union A Γ Lam) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact nat_max_congr (ih1 _) rfl
    | conjRight B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (nat_max_congr (ih1 _) (ih2 _))
    | disjLeft B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm A (.disj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact nat_max_congr
        ((G1nnfProofTree.depth_mpr_left
          (LCS.Finset.insert_comm B A Γ) _ _).trans (ih1 _))
        ((G1nnfProofTree.depth_mpr_left
          (LCS.Finset.insert_comm C A Γ) _ _).trans (ih2 _))
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.cutRank_mpr_left {L : Language} {hL : L.withoutEquality}
    {Γ Γ' Δ : LCS.Finset (FormulaN L)}
    (hidx : Γ = Γ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ' Δ)
    (T : G1nnfProofTree hL Γ' Δ) :
    (@G1nnfProofTree.cutRank L hL Γ Δ
      (@Eq.mpr (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ' Δ) htype T)) =
      (@G1nnfProofTree.cutRank L hL Γ' Δ T) := by
  subst Γ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.cutRank_mp {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ' Δ')
    (T : G1nnfProofTree hL Γ Δ) :
    (@G1nnfProofTree.cutRank L hL Γ' Δ'
      (@Eq.mp (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ' Δ') htype T)) =
      (@G1nnfProofTree.cutRank L hL Γ Δ T) := by
  subst Γ'
  subst Δ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.weakenTreeLeft_cutRank {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v) :
    (T.weakenTreeLeft A hNNF hFV).cutRank = T.cutRank := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    simp only [G1nnfProofTree.weakenTreeLeft]
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_left
        rule Γ Δ A hAxiom hAC hNNF
    have hSpec := Classical.choose_spec hWeakened
    have hGamma :
        ((Classical.choose hWeakened).conclusion Γ Δ).1 =
          LCS.Finset.insert A (rule.conclusion Γ Δ).1 := by
      simpa using congrArg Prod.fst hSpec.2.2
    have hDelta :
        ((Classical.choose hWeakened).conclusion Γ Δ).2 =
          (rule.conclusion Γ Δ).2 := by
      simpa using congrArg Prod.snd hSpec.2.2
    rw [G1nnfProofTree.cutRank_mp hGamma hDelta]
    rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    cases rule with
    | conjLeft1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm A (.conj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm B A Γ) _ _).trans (ih _)
    | conjLeft2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm A (.conj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm C A Γ) _ _).trans (ih _)
    | disjRight1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | disjRight2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | allLeft x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm A (.all x B) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm (formulaSubstN B t x) A Γ) _ _).trans
        (ih _)
    | allRight x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | exLeft x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm A (.ex x B) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm
          (formulaSubstN B (.var y) x) A Γ) _ _).trans (ih _)
    | exRight x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    cases rule with
    | cut B Lam Theta =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_union A Γ Lam) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank, G1nnfRule.cutFormula]
      apply congrArg (fun n => max (B.degree + 1) n)
      exact nat_max_congr (ih1 _) rfl
    | conjRight B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank, G1nnfRule.cutFormula]
      exact nat_max_congr (ih1 _) (ih2 _)
    | disjLeft B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm A (.disj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank, G1nnfRule.cutFormula]
      exact nat_max_congr
        ((G1nnfProofTree.cutRank_mpr_left
          (LCS.Finset.insert_comm B A Γ) _ _).trans (ih1 _))
        ((G1nnfProofTree.cutRank_mpr_left
          (LCS.Finset.insert_comm C A Γ) _ _).trans (ih2 _))
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.depth_mpr_right {L : Language} {hL : L.withoutEquality}
    {Γ Δ Δ' : LCS.Finset (FormulaN L)}
    (hidx : Δ = Δ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ Δ')
    (T : G1nnfProofTree hL Γ Δ') :
    (@G1nnfProofTree.depth L hL Γ Δ
      (@Eq.mpr (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ Δ') htype T)) =
      (@G1nnfProofTree.depth L hL Γ Δ' T) := by
  subst Δ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.weakenTreeRight_depth {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v) :
    (T.weakenTreeRight A hNNF hFV).depth = T.depth := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    simp only [G1nnfProofTree.weakenTreeRight]
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_right
        rule Γ Δ A hAxiom hAC hNNF
    have hSpec := Classical.choose_spec hWeakened
    have hGamma :
        ((Classical.choose hWeakened).conclusion Γ Δ).1 =
          (rule.conclusion Γ Δ).1 := by
      simpa using congrArg Prod.fst hSpec.2.2
    have hDelta :
        ((Classical.choose hWeakened).conclusion Γ Δ).2 =
          LCS.Finset.insert A (rule.conclusion Γ Δ).2 := by
      simpa using congrArg Prod.snd hSpec.2.2
    rw [G1nnfProofTree.depth_mp hGamma hDelta]
    rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    cases rule with
    | conjLeft1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | conjLeft2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | disjRight1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm A (.disj B C) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm B A Δ) _ _).trans (ih _)
    | disjRight2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm A (.disj B C) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm C A Δ) _ _).trans (ih _)
    | allLeft x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | allRight x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm A (.all x B) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm
          (formulaSubstN B (.var y) x) A Δ) _ _).trans (ih _)
    | exLeft x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | exRight x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm A (.ex x B) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm (formulaSubstN B t x) A Δ) _ _).trans
        (ih _)
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    cases rule with
    | cut B Lam Theta =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_union A Δ Theta) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact nat_max_congr
        ((G1nnfProofTree.depth_mpr_right
          (LCS.Finset.insert_comm B A Δ) _ _).trans (ih1 _)) rfl
    | conjRight B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm A (.conj B C) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact nat_max_congr
        ((G1nnfProofTree.depth_mpr_right
          (LCS.Finset.insert_comm B A Δ) _ _).trans (ih1 _))
        ((G1nnfProofTree.depth_mpr_right
          (LCS.Finset.insert_comm C A Δ) _ _).trans (ih2 _))
    | disjLeft B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (nat_max_congr (ih1 _) (ih2 _))
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

end LCS.CutElim.Hauptsatz
end

