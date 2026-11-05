import LCS.Herbrand.HerbrandTheorem.Main.Part1

section

namespace LCS.Herbrand.HerbrandTheorem.Main

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Semantics.Subformulae

open LCS.FirstOrder.Gentzen

open LCS.Herbrand.HerbrandTheorem

open LCS.Herbrand.PrenexForm

open LCS.Herbrand.SharpenedHauptsatz.Theorem

open LCS.CutElim.LK

open LCS.CutElim.LKe.Equivalence

helper /-- Theorem 7.5.1 (companion def): SkolemTermOrder defines the partial ordering on the set HT: t1 < t2 iff t1 is a proper subterm of t2. The Gamma parameter identifies the Herbrand language context. -/
def SkolemTermOrder {L : Language}
    (_gamma : List (FormulaN L))
    (t1 t2 : Term L) : Prop :=
  isProperSubterm t1 t2

helper /-- Theorem 7.5.1 (companion def): Predicate asserting that y is the eigenvariable of some forall:right rule applied somewhere in the FOLK proof tree T. Recurses structurally through the tree and inspects each one-premise rule for `allRight y _ _ _ _ _ _`. -/
def folkProofTreeAllRightEigenvariables {L : Language} :
    {s : Sequent L} → FOLKProofTree s → Nat → Prop
  | _, .axiom_ _ _, _ => False
  | _, .onePremise rule t, y =>
    (match rule with
     | .allRight z _ _ _ _ _ _ => z = y
     | _ => False) ∨ folkProofTreeAllRightEigenvariables t y
  | _, .twoPremise _ t1 t2, y =>
    folkProofTreeAllRightEigenvariables t1 y ∨
    folkProofTreeAllRightEigenvariables t2 y

helper /-- Eigenvariable replacement uses a canonical allocated symbol with ground
arguments at its existential dependencies. The output proof and substitution
live in the extension, and the conclusion is the embedded substitution image. -/
def skolemSubstForEigenvariables {L : Language}
    [BEq L.constSymbols] [Hashable L.constSymbols]
    [Hashable L.funSymbols]
    {sT : Sequent L} (T : FOLKProofTree sT)
    (gamma : List (FormulaN L)) (sd : SkolemData L gamma)
    {sT' : Sequent (validitySkolemLanguage gamma)}
    (_T' : FOLKProofTree sT') : Prop :=
  ∃ (subst : Substitution (validitySkolemLanguage gamma)),
    (∀ x, subst x ≠ Term.var x → IsGroundTerm (subst x)) ∧
    (∀ y, folkProofTreeAllRightEigenvariables T y →
      ∃ (o : UniversalPrefixOccurrence gamma)
        (args : Substitution (validitySkolemLanguage gamma)),
        (∀ k : Fin o.dependencies.length, IsGroundTerm (args (o.dependencies.get k))) ∧
        subst y = Substitution.applyTerm args (skolemTerm sd o)) ∧
    sT'.succedent = sT.succedent.map
      (fun A => Substitution.applyFormula subst (liftValidityFormula gamma A)) ∧
    sT'.antecedent = sT.antecedent.map
      (fun A => Substitution.applyFormula subst (liftValidityFormula gamma A))

helper /-- Example 7.5.3 (companion def): The sequence of maximal elements of HT processed in order: [g(f(a)), f(a), a]. At each step, the maximal element under herbrandExHTOrder is selected and removed. g(f(a)) is maximal first (no term in HT has g(f(a)) as a subterm), then f(a), then a. -/
def herbrandExMaximalElements : List (Term herbrandExLang) :=
  let a := Term.const HerbrandExConst.a
  let fa := Term.func HerbrandExFunc.f (fun _ => a)
  let gfa := Term.func HerbrandExFunc.g (fun _ => fa)
  [gfa, fa, a]

helper /-- Example 7.5.1: whole-term height in this unary example signature.
Constants and variables have height zero; each f or g adds one. -/
def herbrandExTermHeight : Term herbrandExLang → Nat
  | .var _ | .const _ => 0
  | .func symbol ts => herbrandExTermHeight (ts ⟨0, by cases symbol <;> decide⟩) + 1

helper /-- Example 7.5.1: terms paired with their original eigenvariable and actual
node depth, in leaf-to-conclusion order. Addresses are strings of zero edges:
g(f(a)) encodes ∀z at depth 15, f(a) encodes ∀y at 8, a encodes ∀x₁ at 0. -/
def herbrandExTermInferenceSites : List (Term herbrandExLang × Nat × Nat) :=
  let a : Term herbrandExLang := .const .a
  let fa : Term herbrandExLang := .func .f (fun _ => a)
  let gfa : Term herbrandExLang := .func .g (fun _ => fa)
  [(gfa, 3, 15), (fa, 1, 8), (a, 4, 0)]

helper /-- Example 7.5.1: the stored reconstruction order is tied to the original
universal-right occurrences. Within exactly these three entries, greater
whole-term height means an earlier rule (a deeper node above the conclusion).
Bottom-up proof alteration visits the same entries in reverse order. -/
theorem herbrandExTermNestingRuleOrder :
    herbrandExTermInferenceSites.map Prod.fst = herbrandExProofReconstructionOrder ∧
    (herbrandExTermInferenceSites.map Prod.fst).reverse = herbrandExTermSetHT ∧
    (∀ entry ∈ herbrandExTermInferenceSites,
      match LCS.Herbrand.SharpenedHauptsatz.Permutability.lkInferenceAt
        midsequentExampleTree (List.replicate entry.2.2 0) with
      | some (.one (.allRight y x _ _ _ _ _)) => y = entry.2.1 ∧ x = entry.2.1
      | _ => False) ∧
    (∀ u ∈ herbrandExTermInferenceSites, ∀ v ∈ herbrandExTermInferenceSites,
      herbrandExTermHeight v.1 < herbrandExTermHeight u.1 ↔ v.2.2 < u.2.2) := by
  -- REPAIR(T7-130): proof pending
  sorry

helper /-- Example 7.5.3: the two finite maps are inverse, their domain is exactly
HT, and all assigned names avoid every free and bound variable in Γ. -/
theorem herbrandExFreshBijectionSpec :
    (∀ t x, herbrandExFreshName t = some x ↔ herbrandExFreshTerm x = some t) ∧
    (∀ t, t ∈ herbrandExTermSetHT ↔ ∃ x, herbrandExFreshName t = some x) ∧
    (∀ t x, herbrandExFreshName t = some x →
      x ∈ [7, 8, 9] ∧ x ∉ sourceVariableIndices herbrandExampleSequent.succedent) := by
  -- REPAIR(T7-132): proof pending
  sorry

helper /-- Example 7.5.3: H′ is the maximal-term replacement of the actual stored H. -/
theorem herbrandExHPrime_eq_replacement :
    herbrandExHPrime =
      ⟨herbrandExDisjunction.antecedent.map herbrandExReplaceFormula,
        herbrandExDisjunction.succedent.map herbrandExReplaceFormula⟩ := by
  simp only [herbrandExHPrime, herbrandExDisjunction, herbrandExReplaceFormula,
    herbrandExP, herbrandExQ, Sequent.mk.injEq, List.map_cons, List.map_nil,
    List.cons.injEq, FormulaN.neg.injEq, FormulaN.conj.injEq, true_and, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply congrArg (FormulaN.predN (L := herbrandExLang) _)
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl

helper /-- Example 7.5.3: each cumulative prefix contains its named predecessor
at the actual boundary. The third adds one universal step and two exchanges. -/
theorem herbrandExPrefixConnections :
    LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt herbrandExPrefix1 [0] =
      some ⟨herbrandExHPrime, herbrandExHPrimeProof⟩ ∧
    LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt herbrandExPrefix2 [0] =
      some ⟨herbrandExReconstruction1, herbrandExPrefix1⟩ ∧
    LCS.Herbrand.SharpenedHauptsatz.Permutability.lkSubtreeAt herbrandExPrefix3 [0, 0, 0] =
      some ⟨herbrandExReconstruction2, herbrandExPrefix2⟩ := by
  exact ⟨rfl, rfl, rfl⟩

end LCS.Herbrand.HerbrandTheorem.Main

end
