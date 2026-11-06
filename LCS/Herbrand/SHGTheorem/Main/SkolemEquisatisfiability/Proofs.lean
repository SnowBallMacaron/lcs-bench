import LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability

section
namespace LCS.Herbrand.SHGTheorem.Main
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.SHGTheorem
open LCS.Herbrand.SHGTheorem.Herbrand
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem
open LCS.CutElim.Hauptsatz
open LCS.FirstOrder.SemanticsN.Substitution

helper /-- Lemma 7.6.3, property (b): Given M satisfying A, construct an
expansion N of M to the Skolem-extended language such that N satisfies
the Skolem form of A (as packaged in `spec : SkolemSpec L` per
Def 7.6.2). The public `witnessSelectingExpansion` supplies only an
initial interpretation seed `K₀`. The contextual traversal in
`skolemForm_backward_genN` refines `K₀` to a coordinated interpretation
`K`, selecting witnesses while preserving choices made for enclosing
and earlier existential occurrences; the final structure is
`interpretationExpansion spec M K`, not the initial seed expansion.
`A = spec.source` supplies the bridge from
`formulaEvalN M A s` to the input expected by
`skolemForm_backward_genN`. -/
theorem skolem_form_backward {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M A s →
    ∃ (N : Structure spec.language)
      (sN : Assignment N),
      isExpansion L spec.n spec.skolemRank M N ∧
      formulaEvalN N (SK spec) sN :=
-- BEGIN PROOF
by
  intro hA
  -- A = spec.source via hSource, so hA : formulaEvalN M spec.source s.
  rw [hSource] at hA
  exact skolemForm_backward_genN spec M s hA

proof_of skolem_form_sat_iff := by
  -- BEGIN PROOF
    constructor
    · -- Forward: satisfiable A → satisfiable B.
      -- Unpack M, s with M ⊨ A = spec.source, invoke `skolem_form_backward`
      -- so the caller supplies `formulaEvalN M A s`. The output is an
      -- expansion N satisfying `SK spec = B`.
      rintro ⟨M, s, hA⟩
      obtain ⟨N, sN, _hExp, hN⟩ :=
        skolem_form_backward spec A hSource M s hA
      exact ⟨N, sN, _hSkolem ▸ hN⟩
    · -- Backward: satisfiable B → satisfiable A.
      -- Unpack N, sN with N ⊨ B = SK spec. Construct the L-reduct
      -- `M := N|_L`: same carrier, original functions and constants
      -- interpreted through Sum.inl, and the same predicates. Then N is by
      -- construction an expansion of M; apply `skolemForm_forward_genN`
      -- to obtain M ⊨ spec.source = A, hence `satisfiableN A`.
      rintro ⟨N, sN, hB⟩
      let M : Structure L :=
        { carrier := N.carrier
          carrierNonempty := N.carrierNonempty
          interpFunc := fun f args => N.interpFunc (Sum.inl f) args
          interpConst := fun c => N.interpConst (Sum.inl c)
          interpPred := fun P args => N.interpPred P args }
      have hExp : isExpansion L spec.n spec.skolemRank M N :=
        ⟨rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl⟩
      refine ⟨M, sN, ?_⟩
      rw [hSource]
      exact skolemForm_forward_genN spec N sN (_hSkolem ▸ hB) M sN hExp

end LCS.Herbrand.SHGTheorem.Main
end
