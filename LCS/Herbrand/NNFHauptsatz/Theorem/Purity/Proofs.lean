import LCS.Herbrand.NNFHauptsatz.Theorem.Purity

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

open LCS.Herbrand.NNFHauptsatz.G2nnfRule

helper /-- Occurrence-sensitivity regression: the same explicitly weakened atomic subtree is reused in
both premises and contains the same `y`-containing formulae as the root.  The
former formula-value subtraction condition accepts this tree, because every
formula value outside the left premise also appears inside it.  The
occurrence-sensitive condition rejects it because the right premise and root
are distinct occurrences. -/
theorem duplicateVariableFormulaOutsideOccurrence_rejected
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (A : FormulaN L) (hAtom : A.isAtomic) (y : Nat)
    (hy : Membership.mem (formulaAllVariables A) y) :
    let Γ : LCS.Finset (FormulaN L) :=
      LCS.Finset.insert A ∅
    let Δ : LCS.Finset (FormulaN L) :=
      LCS.Finset.singleton (.conj A A)
    let hAqf : isQuantifierFree A :=
      AllRectified.isQuantifierFree_of_isAtomic A hAtom
    let hConjQf : isQuantifierFree (.conj A A) := ⟨hAqf, hAqf⟩
    let hSubRect : AllRectified (Γ, LCS.Finset.insert A Δ) :=
      AllRectified.of_allQuantifierFree _ ⟨
        (by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with rfl | hF
          · exact hAqf
          · exact (LCS.Finset.not_mem_empty hF).elim),
        (by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with rfl | hF
          · exact hAqf
          · rw [LCS.Finset.mem_singleton] at hF
            subst F
            exact hConjQf)⟩
    let hRootRect :
        AllRectified (Γ, LCS.Finset.insert (.conj A A) Δ) :=
      AllRectified.of_allQuantifierFree _ ⟨
        (by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with rfl | hF
          · exact hAqf
          · exact (LCS.Finset.not_mem_empty hF).elim),
        (by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with rfl | hF
          · exact hConjQf
          · rw [LCS.Finset.mem_singleton] at hF
            subst F
            exact hConjQf)⟩
    let hAnnf : A.isNNF := by
      cases A with
      | predN _ _ => trivial
      | eq_ _ _ _ => trivial
      | neg _ | conj _ _ | disj _ _ | impl _ _ | all _ _ | ex _ _ =>
          exact Bool.noConfusion hAtom
    let hSubNNF : AllNNF (Γ, LCS.Finset.insert A Δ) :=
      ⟨(by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with rfl | hF
          · exact hAnnf
          · exact (LCS.Finset.not_mem_empty hF).elim),
        (by
          intro F hF
          rcases LCS.Finset.mem_insert.mp hF with rfl | hF
          · exact hAnnf
          · rw [LCS.Finset.mem_singleton] at hF
            subst F
            exact ⟨hAnnf, hAnnf⟩)⟩
    let hRootNNF : AllNNF (Γ, LCS.Finset.insert (.conj A A) Δ) :=
      ⟨hSubNNF.1, by
        intro F hF
        rcases LCS.Finset.mem_insert.mp hF with rfl | hF
        · exact ⟨hAnnf, hAnnf⟩
        · rw [LCS.Finset.mem_singleton] at hF
          subst F
          exact ⟨hAnnf, hAnnf⟩⟩
    let hBareNNF : AllNNF (Γ, Γ) := ⟨hSubNNF.1, hSubNNF.1⟩
    let hBareRect : AllRectified (Γ, Γ) := ⟨hSubRect.1, hSubRect.1⟩
    let bare : G2nnfProofTree hL Γ Γ :=
      .axiom_ (.axiomPosId A hAtom ∅ ∅) ⟨rfl, rfl⟩ rfl
        ⟨trivial, hBareNNF, (by intro seq h; cases h), hBareRect⟩
    let hOrder : LCS.Finset.insert (.conj A A) Γ = LCS.Finset.insert A Δ := by
      apply LCS.Finset.ext
      intro F
      simp only [Γ, Δ, LCS.Finset.mem_insert, LCS.Finset.mem_singleton]
      constructor
      · rintro (h | h | h)
        · exact Or.inr h
        · exact Or.inl h
        · exact (LCS.Finset.not_mem_empty h).elim
      · rintro (h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
    let hWeakSC : (G2nnfRuleCore.weakRight (.conj A A) Γ Γ).SideConditions :=
      ⟨trivial, (by change AllNNF (Γ, LCS.Finset.insert (.conj A A) Γ); rw [hOrder]; exact hSubNNF),
        (by intro seq h; simp only [G2nnfRuleCore.premises, List.mem_cons,
              List.not_mem_nil, or_false] at h; subst seq; exact hBareNNF),
        (by change AllRectified (Γ, LCS.Finset.insert (.conj A A) Γ); rw [hOrder]; exact hSubRect)⟩
    let hRootSC : (G2nnfRuleCore.conjRight A A Γ Δ).SideConditions :=
      ⟨trivial, hRootNNF,
        (by intro seq h; simp only [G2nnfRuleCore.premises, List.mem_cons,
              List.not_mem_nil, or_false, or_self] at h; subst seq; exact hSubNNF), hRootRect⟩
    let sub : G2nnfProofTree hL Γ (LCS.Finset.insert A Δ) :=
      G2nnfProofTree.castTree (hL := hL) rfl hOrder
        (.onePremise (.weakRight (.conj A A) Γ Γ) trivial rfl hWeakSC bare)
    let root : G2nnfProofTree hL Γ
        (LCS.Finset.insert (.conj A A) Δ) :=
      .twoPremise (.conjRight A A Γ Δ) trivial rfl hRootSC sub sub
    let left : NodeOccurrence root Γ (LCS.Finset.insert A Δ) :=
      ⟨sub, .leftPremise (.conjRight A A Γ Δ) trivial rfl hRootSC
        sub sub (.root sub)⟩
    (∀ f : FormulaN L,
      g2nnfProofTreeContainsFormula root f →
      ¬ g2nnfProofTreeContainsFormula (hL := hL) sub f →
      ¬ Membership.mem (formulaAllVariables f) y) ∧
    ¬ g2nnfEigenvariableOccursOnlyInSubtree y left := by
  dsimp only
  constructor
  · intro f hRoot hNotSub
    apply False.elim
    apply hNotSub
    simp only [g2nnfProofTreeContainsFormula] at hRoot
    rcases hRoot with hΓ | hΔ | hSub | hSub
    · exact g2nnfProofTreeContainsFormula_of_root _ f (Or.inl hΓ)
    · apply g2nnfProofTreeContainsFormula_of_root _ f
      exact Or.inr (LCS.Finset.mem_insert.mpr
        (Or.inr ((LCS.Finset.mem_singleton f (.conj A A)).mpr
          ((LCS.Finset.mem_insert.mp hΔ).elim id
            (fun h => (LCS.Finset.mem_singleton f (.conj A A)).mp h)))))
    · exact hSub
    · exact hSub
  · intro hOnly
    exact hOnly.1 A
      (Or.inl (LCS.Finset.mem_insert.mpr (Or.inl rfl))) hy

helper /-- Positive occurrence regression: if `y` occurs in a formula inside the
sole premise subtree but the inference conclusion is `y`-free, that exact
premise occurrence is accepted.  The target subtree itself is deliberately
not inspected by the outside-occurrence condition. -/
theorem variableConfinedToExactPremiseOccurrence_accepted
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (y : Nat) (rule : G2nnfRuleCore L)
    (hAdmit : rule.BareAtomicAxiom)
    (hPrem : (rule.premises).length = 1)
    (hSC : G2nnfRuleCore.SideConditions rule)
    (sub : G2nnfProofTree hL
      ((rule.premises)[0]'(by omega)).1
      ((rule.premises)[0]'(by omega)).2)
    (f : FormulaN L) (hf : g2nnfProofTreeContainsFormula (hL := hL) sub f)
    (hy : Membership.mem (formulaAllVariables f) y)
    (hConclusion : g2nnfSequentVariableFree y
      (rule.conclusion).1
      (rule.conclusion).2) :
    let root :=
      G2nnfDeductionTreeCore.onePremise rule hAdmit hPrem hSC sub
    let occurrence : NodeOccurrence root _ _ :=
      ⟨sub, .onePremise rule hAdmit hPrem hSC sub (.root sub)⟩
    g2nnfProofTreeContainsFormula (hL := hL) sub f ∧
    Membership.mem (formulaAllVariables f) y ∧
    g2nnfEigenvariableOccursOnlyInSubtree y occurrence := by
  dsimp only
  exact ⟨hf, hy, hConclusion, trivial⟩

helper /-- Nested-quantifier regression: even when an `allSubRight` node is reached
below other inferences, its premise occurrence is formed by composing the
current path with the quantifier-premise step.  Thus the eigenvariable check
still ranges over the fixed whole tree `outer`, rather than restarting at the
nested quantifier node. -/
theorem nestedAllSubRightUsesWholeTreeOccurrence
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (A B : FormulaN L) (occurrence : MaxQuantifierOccurrence A)
    (x y : Nat)
    (hSelected : occurrence.selected = FormulaN.all x B)
    (Gamma Delta : LCS.Finset (FormulaN L))
    (hPrem :
      ((G2nnfRuleCore.allSubRight A occurrence x B y hSelected Gamma Delta).premises).length = 1)
    (hSC : G2nnfRuleCore.SideConditions
      (.allSubRight A occurrence x B y hSelected Gamma Delta))
    (sub : G2nnfProofTree hL
      (((G2nnfRuleCore.allSubRight A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).1
      (((G2nnfRuleCore.allSubRight A occurrence x B y hSelected Gamma Delta).premises)[0]'(by omega)).2)
    {Γroot Δroot : LCS.Finset (FormulaN L)}
    (outer : G2nnfProofTree hL Γroot Δroot)
    (path : RootToNodePath outer
      (.onePremise (.allSubRight A occurrence x B y hSelected Gamma Delta) trivial
        hPrem hSC sub)) :
    isPureVariableProofG2nnfAux outer
        (.onePremise (.allSubRight A occurrence x B y hSelected Gamma Delta) trivial
          hPrem hSC sub) path →
      g2nnfEigenvariableOccursOnlyInSubtree y
        (⟨sub, path.trans
          (.onePremise
            (.allSubRight A occurrence x B y hSelected Gamma Delta) trivial
            hPrem hSC sub (.root sub))⟩ :
          NodeOccurrence outer _ _) := by
  intro hPure
  exact hPure.1.2

proof_of g2nnf_pureVariableConversion := by
  -- REPAIR(T7-RG): proof pending; rename eigenvariables subtree by subtree as in Lemma 7.3.1, transferred to the G2nnf quantifier rules
  sorry

proof_of g2nnf_hasBareAtomicLeaves := by
  induction T with
  | leaf Γ Δ hOpen hNNF hRect => exact hOpen.elim
  | extraAxiom Γ Δ hExtra hNNF hRect => exact hExtra.elim
  | axiom_ rule hAdmit hAx hSC =>
    change IsBareAtomicLeafSequent hL rule.conclusion
    cases rule with
    | axiomPosId A hAtom Γ Δ =>
      rcases hAdmit with ⟨rfl, rfl⟩
      exact ⟨A, hAtom, Or.inl rfl⟩
    | axiomNegId A hAtom Γ Δ =>
      rcases hAdmit with ⟨rfl, rfl⟩
      exact ⟨A, hAtom, Or.inr (Or.inr (Or.inr rfl))⟩
    | axiomCompRight A hAtom Γ Δ =>
      rcases hAdmit with ⟨rfl, rfl⟩
      exact ⟨A, hAtom, Or.inr (Or.inl rfl)⟩
    | axiomCompLeft A hAtom Γ Δ =>
      rcases hAdmit with ⟨rfl, rfl⟩
      exact ⟨A, hAtom, Or.inr (Or.inr (Or.inl rfl))⟩
    | _ => simp [G2nnfRuleCore.premises] at hAx
  | onePremise rule hAdmit hPrem hSC sub ih => exact ih
  | twoPremise rule hAdmit hPrem hSC left right ihLeft ihRight =>
    exact ⟨ihLeft, ihRight⟩


helper /-- The atomic-leaf extension retains the same end sequent and the very same
proof tree. This is the atomic-leaf assertion, separate from the deferred
conversion of an arbitrary proof to a pure-variable proof. -/
theorem g2nnf_atomicLeafExtension {L : Language} {hL : L.withoutEquality}
    [DecidableEq (FormulaN L)] {Γ Δ : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Γ Δ) :
    ∃ T' : G2nnfProofTree hL Γ Δ, T' = T ∧ HasBareAtomicLeaves (hL := hL) T' :=
  ⟨T, rfl, g2nnf_hasBareAtomicLeaves (hL := hL) T⟩

end LCS.Herbrand.NNFHauptsatz.Theorem

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

open LCS.Herbrand.NNFHauptsatz.G2nnfRule

namespace G2nnfPermutationLowerRuleView

end G2nnfPermutationLowerRuleView

end LCS.Herbrand.NNFHauptsatz.Theorem

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

open LCS.Herbrand.NNFHauptsatz.G2nnfRule

namespace G2nnfOtherPremiseFrontier

helper /-- Canonical alpha-copy path for the exact non-selected frontier. -/
noncomputable def G2nnfOtherPremiseFrontier.freshAlphaCopyPath
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaSelected DeltaSelected Gamma Delta :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {R₂ : G2nnfRuleCore L}
    {selectedTree : G2nnfProofTree hL GammaSelected DeltaSelected}
    {selected :
      G2nnfSelectedPremiseOccurrence root R₂ selectedTree}
    {other : G2nnfProofTree hL Gamma Delta}
    (frontier : G2nnfOtherPremiseFrontier selected other)
    (avoid : LCS.Finset Nat) :
    RootToNodePath (root.freshAlphaCopy avoid)
      (other.varMap (root.freshAlphaRenaming avoid)
        (root.freshAlphaRenaming_injective avoid)) :=
  frontier.path.freshAlphaCopy avoid

helper /-- Canonical alpha-copy node occurrence for the exact non-selected
frontier.  This is the B.3 bridge used symmetrically for binary
`allSubRight` and `exSubLeft` duplication cases. -/
noncomputable def G2nnfOtherPremiseFrontier.freshAlphaCopyOccurrence
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {GammaRoot DeltaRoot GammaSelected DeltaSelected Gamma Delta :
      LCS.Finset (FormulaN L)}
    {root : G2nnfProofTree hL GammaRoot DeltaRoot}
    {R₂ : G2nnfRuleCore L}
    {selectedTree : G2nnfProofTree hL GammaSelected DeltaSelected}
    {selected :
      G2nnfSelectedPremiseOccurrence root R₂ selectedTree}
    {other : G2nnfProofTree hL Gamma Delta}
    (frontier : G2nnfOtherPremiseFrontier selected other)
    (avoid : LCS.Finset Nat) :
    NodeOccurrence (root.freshAlphaCopy avoid)
      (formulaFinsetVarMapN (root.freshAlphaRenaming avoid) Gamma)
      (formulaFinsetVarMapN (root.freshAlphaRenaming avoid) Delta) :=
  frontier.occurrence.freshAlphaCopy avoid

end G2nnfOtherPremiseFrontier

end LCS.Herbrand.NNFHauptsatz.Theorem

end

section

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.Herbrand.NNFHauptsatz

open LCS.Herbrand.NNFHauptsatz.Soundness

open LCS.Herbrand.SharpenedHauptsatz

open LCS.Herbrand.SharpenedHauptsatz.Permutability

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.Herbrand.PrenexForm

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Completeness

open LCS.CutElim.LK

namespace LCS.Herbrand.NNFHauptsatz.Theorem

open LCS.Herbrand.NNFHauptsatz.G2nnfProofTree

open LCS.Herbrand.NNFHauptsatz.G2nnfRule

namespace G2nnfSelectedPremiseOccurrence



end G2nnfSelectedPremiseOccurrence

end LCS.Herbrand.NNFHauptsatz.Theorem

end
