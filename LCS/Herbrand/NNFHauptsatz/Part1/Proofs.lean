import LCS.Herbrand.NNFHauptsatz.Part1

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

namespace AllRectified



















end AllRectified

end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

namespace MaxQuantifierOccurrence



helper /-- Looking up the address of an occurrence recovers its selected formula. -/
theorem MaxQuantifierOccurrence.lookup_address {L : Language} {A : FormulaN L}
    (occurrence : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A) :
    lookup A occurrence.address = some occurrence.selected := by
  induction occurrence with
  | all _ _ => rfl
  | ex _ _ => rfl
  | conjLeft _ _ ih => exact ih
  | conjRight _ _ ih => exact ih
  | disjLeft _ _ ih => exact ih
  | disjRight _ _ ih => exact ih

helper /-- After selected replacement, the same address looks up the replacement. -/
theorem MaxQuantifierOccurrence.lookup_replace {L : Language} {A : FormulaN L}
    (occurrence : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A) (replacement : FormulaN L) :
    lookup (occurrence.replace replacement) occurrence.address =
      some replacement := by
  induction occurrence with
  | all _ _ =>
      simpa only [replace, address, lookup]
  | ex _ _ =>
      simpa only [replace, address, lookup]
  | conjLeft _ _ ih => exact ih
  | conjRight _ _ ih => exact ih
  | disjLeft _ _ ih => exact ih
  | disjRight _ _ ih => exact ih

helper /-- Free variables of the selected formula already occur free in the ambient
formula.  No enclosing quantifier can intervene along a maximal occurrence
path. -/
theorem MaxQuantifierOccurrence.selected_fv_subset {L : Language} {A : FormulaN L}
    (occurrence : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A) :
    formulaFVN occurrence.selected ⊆ formulaFVN A := by
  induction occurrence with
  | all _ _ =>
      intro v hv
      exact hv
  | ex _ _ =>
      intro v hv
      exact hv
  | conjLeft _ _ ih =>
      intro v hv
      exact Or.inl (ih v hv)
  | conjRight _ _ ih =>
      intro v hv
      exact Or.inr (ih v hv)
  | disjLeft _ _ ih =>
      intro v hv
      exact Or.inl (ih v hv)
  | disjRight _ _ ih =>
      intro v hv
      exact Or.inr (ih v hv)

helper /-- Selected replacement introduces no free variable outside the ambient
formula or the replacement formula. -/
theorem MaxQuantifierOccurrence.replace_fv_subset {L : Language} {A : FormulaN L}
    (occurrence : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A) (replacement : FormulaN L) :
    formulaFVN (occurrence.replace replacement) ⊆
      formulaFVN A ∪ formulaFVN replacement := by
  induction occurrence with
  | all _ _ =>
      intro v hv
      exact Or.inr hv
  | ex _ _ =>
      intro v hv
      exact Or.inr hv
  | conjLeft _ _ ih =>
      intro v hv
      rcases hv with hv | hv
      · rcases ih v hv with hv | hv
        · exact Or.inl (Or.inl hv)
        · exact Or.inr hv
      · exact Or.inl (Or.inr hv)
  | conjRight _ _ ih =>
      intro v hv
      rcases hv with hv | hv
      · exact Or.inl (Or.inl hv)
      · rcases ih v hv with hv | hv
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv
  | disjLeft _ _ ih =>
      intro v hv
      rcases hv with hv | hv
      · rcases ih v hv with hv | hv
        · exact Or.inl (Or.inl hv)
        · exact Or.inr hv
      · exact Or.inl (Or.inr hv)
  | disjRight _ _ ih =>
      intro v hv
      rcases hv with hv | hv
      · exact Or.inl (Or.inl hv)
      · rcases ih v hv with hv | hv
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv

helper /-- Selected replacement introduces no bound variable outside the ambient
formula or the replacement formula. -/
theorem MaxQuantifierOccurrence.replace_bv_subset {L : Language} {A : FormulaN L}
    (occurrence : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A) (replacement : FormulaN L) :
    formulaBVN (occurrence.replace replacement) ⊆
      formulaBVN A ∪ formulaBVN replacement := by
  induction occurrence with
  | all _ _ =>
      intro v hv
      exact Or.inr hv
  | ex _ _ =>
      intro v hv
      exact Or.inr hv
  | conjLeft _ _ ih =>
      intro v hv
      rcases hv with hv | hv
      · rcases ih v hv with hv | hv
        · exact Or.inl (Or.inl hv)
        · exact Or.inr hv
      · exact Or.inl (Or.inr hv)
  | conjRight _ _ ih =>
      intro v hv
      rcases hv with hv | hv
      · exact Or.inl (Or.inl hv)
      · rcases ih v hv with hv | hv
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv
  | disjLeft _ _ ih =>
      intro v hv
      rcases hv with hv | hv
      · rcases ih v hv with hv | hv
        · exact Or.inl (Or.inl hv)
        · exact Or.inr hv
      · exact Or.inl (Or.inr hv)
  | disjRight _ _ ih =>
      intro v hv
      rcases hv with hv | hv
      · exact Or.inl (Or.inl hv)
      · rcases ih v hv with hv | hv
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv

helper /-- A maximal occurrence address cannot be a strict prefix of another maximal
occurrence address in the same ambient formula. -/
theorem MaxQuantifierOccurrence.eq_of_address_prefix {L : Language} {A : FormulaN L}
    (first second : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A)
    (hPrefix : first.address <+: second.address) :
    first = second := by
  induction first with
  | all _ _ =>
      cases second
      rfl
  | ex _ _ =>
      cases second
      rfl
  | conjLeft first _ ih =>
      cases second with
      | conjLeft second _ =>
          have hInner : first.address <+: second.address := by
            rcases hPrefix with ⟨suffix, hAddress⟩
            exact ⟨suffix, (List.cons.inj hAddress).2⟩
          cases ih second hInner
          rfl
      | conjRight _ _ =>
          rcases hPrefix with ⟨suffix, hAddress⟩
          exact nomatch (List.cons.inj hAddress).1
  | conjRight _ first ih =>
      cases second with
      | conjLeft _ _ =>
          rcases hPrefix with ⟨suffix, hAddress⟩
          exact nomatch (List.cons.inj hAddress).1
      | conjRight _ second =>
          have hInner : first.address <+: second.address := by
            rcases hPrefix with ⟨suffix, hAddress⟩
            exact ⟨suffix, (List.cons.inj hAddress).2⟩
          cases ih second hInner
          rfl
  | disjLeft first _ ih =>
      cases second with
      | disjLeft second _ =>
          have hInner : first.address <+: second.address := by
            rcases hPrefix with ⟨suffix, hAddress⟩
            exact ⟨suffix, (List.cons.inj hAddress).2⟩
          cases ih second hInner
          rfl
      | disjRight _ _ =>
          rcases hPrefix with ⟨suffix, hAddress⟩
          exact nomatch (List.cons.inj hAddress).1
  | disjRight _ first ih =>
      cases second with
      | disjLeft _ _ =>
          rcases hPrefix with ⟨suffix, hAddress⟩
          exact nomatch (List.cons.inj hAddress).1
      | disjRight _ second =>
          have hInner : first.address <+: second.address := by
            rcases hPrefix with ⟨suffix, hAddress⟩
            exact ⟨suffix, (List.cons.inj hAddress).2⟩
          cases ih second hInner
          rfl

helper /-- Distinct maximal occurrence witnesses have incomparable addresses. -/
theorem MaxQuantifierOccurrence.addresses_incomparable_of_ne {L : Language} {A : FormulaN L}
    {first second : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A} (hne : first ≠ second) :
    ¬ first.address <+: second.address ∧
      ¬ second.address <+: first.address := by
  constructor
  · intro hPrefix
    exact hne (eq_of_address_prefix first second hPrefix)
  · intro hPrefix
    exact hne (eq_of_address_prefix second first hPrefix).symm



helper /-- Adversarial duplicate regression: equal branch syntax still yields two
different occurrence witnesses, and selected replacement changes only the
chosen copy. -/
theorem MaxQuantifierOccurrence.duplicate_conj_regression {L : Language} {A : FormulaN L}
    (occurrence : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence A) (replacement : FormulaN L) :
    let left : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence (.conj A A) :=
      .conjLeft occurrence A
    let right : _root_.LCS.Herbrand.NNFHauptsatz.MaxQuantifierOccurrence (.conj A A) :=
      .conjRight A occurrence
    left ≠ right ∧
      left.selected = right.selected ∧
      left.replace replacement = .conj (occurrence.replace replacement) A ∧
      right.replace replacement = .conj A (occurrence.replace replacement) := by
  dsimp
  refine ⟨?_, rfl, rfl, rfl⟩
  intro h
  cases h

end MaxQuantifierOccurrence

end LCS.Herbrand.NNFHauptsatz

end

section

namespace LCS.Herbrand.NNFHauptsatz

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.CutElim.Hauptsatz

open LCS.CutElim.Hauptsatz.Equality

section QuantifierPolarity

proof_of quantifierOccurrence_ruleKind := set_option backward.isDefEq.respectTransparency false in
  by
    rcases o.normalization true with ⟨q, ha, hs⟩
    refine ⟨q, ha, ?_, ?_⟩
    · cases negative <;> simpa using hs
    · rw [hs]
      cases side <;> cases k <;> cases negative <;> rfl


proof_of quantifierPolarityEx_ruleKind := set_option backward.isDefEq.respectTransparency false in
  by
    refine ⟨rfl, ?_⟩
    exact quantifierOccurrence_ruleKind (L := qPolExLang) rfl quantifierPolarityExOccurrence .antecedent


proof_of quantifierPolarityEx_equiv := set_option backward.isDefEq.respectTransparency false in
  FormulaN.toNNF_equiv quantifierPolarityExFormula


end QuantifierPolarity

end LCS.Herbrand.NNFHauptsatz

end
