import LCS.Herbrand.NNFHauptsatz.Theorem.Example

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

noncomputable section

helper /-- Example 7.4.4: every terminal sequent in the concrete normal proof is
one of the bare atomic schemes. Context formulae above the selected
midsequent are supplied by explicit weakening inferences. -/
theorem nnfHauptsatzExNormalTree_bareLeaves :
    HasBareAtomicLeaves (hL := by rfl) nnfHauptsatzExNormalTree :=
  g2nnf_hasBareAtomicLeaves nnfHauptsatzExNormalTree

end

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

proof_of g2nnf_permutability := by
  -- BEGIN PROOF
    -- REPAIR(T7-47): proof pending; construct Q for each eligible occurrence
    sorry


proof_of g1nnf_subsystem_g2nnf := by
  -- REPAIR(T7-RB): proof pending; every G1nnf inference is simulated by G2nnf inferences (G1nnf ⊆ G2nnf)
  sorry


helper /-- Index casts do not alter branch order or branch strings. -/
theorem StringEncoding_castTree
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta Gamma' Delta' : LCS.Finset (FormulaN L)}
    (hGamma : Gamma = Gamma') (hDelta : Delta = Delta')
    (T : G2nnfProofTree hL Gamma Delta) :
    StringEncoding (hL := hL) (T.castTree hGamma hDelta) = StringEncoding (hL := hL) T := by
  subst Gamma'
  subst Delta'
  rfl

helper /-- Uniform injective renaming preserves the exact list of branch strings,
including left-before-right binary branch order. -/
theorem StringEncoding_varMap
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    (ρ : Nat → Nat) (hρ : Function.Injective ρ)
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta) :
    StringEncoding (hL := hL) (T.varMap ρ hρ) = StringEncoding (hL := hL) T := by
  induction T with
  | leaf _ _ h _ _ => exact h.elim
  | extraAxiom _ _ h _ _ => exact h.elim
  | axiom_ rule hAdmit hAxiom hSC =>
      simp only [G2nnfProofTree.varMap]
      refine (StringEncoding_castTree _ _ _).trans ?_
      simp only [StringEncoding]
  | onePremise rule hAdmit hPrem hSC sub ih =>
      simp only [G2nnfProofTree.varMap]
      refine (StringEncoding_castTree _ _ _).trans ?_
      simp only [StringEncoding_castTree,
        StringEncoding, G2nnfRuleCore.isQuantifierRuleBool_varMap, ih]
  | twoPremise rule hAdmit hPrem hSC sub1 sub2 ih1 ih2 =>
      simp only [G2nnfProofTree.varMap]
      refine (StringEncoding_castTree _ _ _).trans ?_
      simp only [StringEncoding_castTree,
        StringEncoding, G2nnfRuleCore.isQuantifierRuleBool_varMap, ih1, ih2]

helper /-- Canonical alpha copying preserves the exact string encoding. -/
theorem StringEncoding_freshAlphaCopy
    {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)]
    {Gamma Delta : LCS.Finset (FormulaN L)}
    (T : G2nnfProofTree hL Gamma Delta)
    (avoid : LCS.Finset Nat) :
    StringEncoding (hL := hL) (T.freshAlphaCopy avoid) = StringEncoding (hL := hL) T := by
  rw [freshAlphaCopy, StringEncoding_castTree, StringEncoding_varMap]

helper /-- Theorem 7.4.1 (companion def): Finds the premise of the highest (closest to root) quantifier inference in a normalized G2nnf proof tree. In a normal form proof (where all quantifier rules are below all propositional/weakening rules), this is the midsequent candidate M. Returns None if the tree contains no quantifier rules. -/
def premiseOfHighestQuantifier {L : Language} {hL : L.withoutEquality} [DecidableEq (FormulaN L)] :
    {Γ Δ : LCS.Finset (FormulaN L)} →
    G2nnfProofTree hL Γ Δ →
    Option (LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L))
  | _, _, .leaf _ _ h _ _ => h.elim
  | _, _, .extraAxiom _ _ h _ _ => h.elim
  | _, _, .axiom_ _ _ _ _ => none
  | _, _, .onePremise rule _ _ _ sub =>
    if G2nnfRuleCore.isQuantifierRuleBool rule then
      match premiseOfHighestQuantifier (hL := hL) sub with
      | some mid => some mid
      | none => some (G2nnfProofTree.conclusion (hL := hL) sub)
    else premiseOfHighestQuantifier (hL := hL) sub
  | _, _, .twoPremise rule _ _ _ sub1 sub2 =>
    if G2nnfRuleCore.isQuantifierRuleBool rule then
      match premiseOfHighestQuantifier (hL := hL) sub1,
            premiseOfHighestQuantifier (hL := hL) sub2 with
      | some mid, _ => some mid
      | _, some mid => some mid
      | none, none => some (G2nnfProofTree.conclusion (hL := hL) sub1)
    else
      match premiseOfHighestQuantifier (hL := hL) sub1 with
      | some mid => some mid
      | none => premiseOfHighestQuantifier (hL := hL) sub2

helper /-- Theorem 7.4.1 (companion def): Given the midsequent candidate M (a pair of `LCS.Finset (FormulaN L)`), removes any quantified subformulae that were introduced by weakening above M, yielding the actual midsequent Gamma' -> Delta' with only quantifier-free formulae. A formula is retained only if it is quantifier-free (isQuantifierFree). This corresponds to the textbook's step of removing weakening-introduced quantified formulae from M to form the actual midsequent. The output representation uses `Set (FormulaN L)` to capture the "membership + predicate" filter; in downstream code this may be re-inserted into an `LCS.Finset` via a decidable predicate or used directly at the set level. -/
def removeWeakeningQuantifiedFormulae {L : Language}
    (seq : LCS.Finset (FormulaN L) × LCS.Finset (FormulaN L)) :
    Set (FormulaN L) × Set (FormulaN L) :=
  ( fun A => Membership.mem seq.1 A ∧
      FirstOrder.SemanticsN.isQuantifierFree A,
    fun A => Membership.mem seq.2 A ∧
      FirstOrder.SemanticsN.isQuantifierFree A )

proof_of sharpenedHauptsatz_G2nnf := by
  -- REPAIR(T6-21c): truth open under E-CUTFB; proof pending
  -- REPAIR(T7-20): proof pending; existing case/conversion proof debt
  sorry


helper /-- Example 7.4.4 (companion theorem): Verifies that every formula in the midsequent nnfHauptsatzExMidsequent is quantifier-free, illustrating property (1) of Theorem 7.4.1. The midsequent formulae P(a) or (Q(a) or R(f(a))) and P(a) or (Q(a) or R(f(b))) in the antecedent and P(a), Q(a), R(f(a)) and R(f(b)) in the succedent are all built from atomic predicates and propositional connectives without quantifiers. -/
theorem nnfHauptsatzExMidsequentIsQuantifierFree :
    (∀ A, A ∈ nnfHauptsatzExMidsequent.antecedent →
      FirstOrder.SemanticsN.isQuantifierFree A) ∧
    (∀ A, A ∈ nnfHauptsatzExMidsequent.succedent →
      FirstOrder.SemanticsN.isQuantifierFree A) := by
-- BEGIN PROOF
  constructor
  · intro A hA
    simp only [nnfHauptsatzExMidsequent, List.mem_cons,
      List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl
    · trivial
    · trivial
  · intro A hA
    simp only [nnfHauptsatzExMidsequent, List.mem_cons,
      List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl
    · trivial
    · trivial
    · exact ⟨trivial, trivial⟩

helper theorem nnfHauptExMidFinsetQuantifierFree :
    (∀ A, A ∈ nnfHauptExMidGamma →
      FirstOrder.SemanticsN.isQuantifierFree A) ∧
    (∀ A, A ∈ nnfHauptExDelta →
      FirstOrder.SemanticsN.isQuantifierFree A) := by
  constructor
  · intro A hA
    change A ∈ LCS.Finset.insert nnfHauptEx_midAnt1
      (LCS.Finset.insert nnfHauptEx_midAnt2
        LCS.Finset.empty) at hA
    rcases LCS.Finset.mem_insert.mp hA with rfl | hA
    · exact ⟨trivial, ⟨trivial, trivial⟩⟩
    · rcases LCS.Finset.mem_insert.mp hA with rfl | hA
      · exact ⟨trivial, ⟨trivial, trivial⟩⟩
      · exact (LCS.Finset.not_mem_empty hA).elim
  · intro A hA
    change A ∈ LCS.Finset.insert nnfHauptEx_Pa
      (LCS.Finset.insert nnfHauptEx_Qa
        (LCS.Finset.insert nnfHauptEx_RfaAndRfb
          LCS.Finset.empty)) at hA
    rcases LCS.Finset.mem_insert.mp hA with rfl | hA
    · trivial
    · rcases LCS.Finset.mem_insert.mp hA with rfl | hA
      · trivial
      · rcases LCS.Finset.mem_insert.mp hA with rfl | hA
        · exact ⟨trivial, trivial⟩
        · exact (LCS.Finset.not_mem_empty hA).elim


-- BEGIN PROOF
proof_of nnfHauptsatzExIsMidsequent := by
  let occurrence :
      G2nnfProofTree.NodeOccurrence nnfHauptsatzExNormalTree
        nnfHauptExMidGamma nnfHauptExDelta :=
    ⟨nnfHauptExNormalConstruction.node,
      nnfHauptExNormalConstruction.path⟩
  exact
    ⟨nnfHauptExMidFinsetQuantifierFree,
      ⟨occurrence, nnfHauptExNormalConstruction.above,
        nnfHauptExNormalConstruction.below⟩⟩

end LCS.Herbrand.NNFHauptsatz.Theorem

end
