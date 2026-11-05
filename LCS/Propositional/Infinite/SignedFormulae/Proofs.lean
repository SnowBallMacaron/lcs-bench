import LCS.Propositional.Infinite.SignedFormulae

namespace LCS.Propositional.Infinite.SignedFormulae

open LCS.Propositional.Syntax

open LCS.Propositional.Semantics

open LCS.Propositional.Systems.G

open LCS.Propositional.Systems.G.Search

open LCS.Propositional.Infinite

open Classical

proof_of sequentsAlongPath_ne_nil := by
  -- BEGIN PROOF
    cases dt with
    | leaf s => simp [sequentsAlongPath]
    | onePremise _ child => simp [sequentsAlongPath]
    | twoPremise _ left right =>
      cases p with
      | nil => simp [sequentsAlongPath]
      | cons d rest =>
        cases d with
        | left => simp [sequentsAlongPath]
        | right => simp [sequentsAlongPath]


proof_of hintikka_set_satisfiable := by
  -- BEGIN PROOF
    refine ⟨hintikkaCanonicalValuation S, fun sf hsf => ?_⟩
    have hAux := canonical_satisfies_combined S hS
    cases sf with
    | trueF A => exact (hAux A).1 hsf
    | falseF A => exact (hAux A).2 hsf


helper /-- Theorem 3.5.1 (infrastructure for future proving): If an infinite
    sequent is falsifiable, then there exists a Hintikka set and
    falsifying valuation. This is a semantic-only companion that
    bypasses `infSearch`; the main textbook statement
    `search_theorem_3_5_1` binds the falsifying valuation to an
    `infSearchSteps`-produced tree. -/
theorem infinite_sequent_falsifiable_case (seq : InfSequent)
    (h : infSeqFalsifiable seq)
    : ∃ (S : Set SignedFormula), IsHintikkaSet S ∧
      (∃ v : Valuation, SignedSet.satisfiedBy S v ∧ infSeqFalsifies v seq) :=
-- BEGIN PROOF
by
  obtain ⟨v, hv⟩ := h
  let S : Set SignedFormula := fun sf => match sf with
    | .trueF A => evalExtN v A = BoolVal.T
    | .falseF A => evalExtN v A = BoolVal.F
  refine ⟨S, ?hintikka, v, ?sat, hv⟩
  case hintikka =>
    refine ⟨?_, ?_, ?_⟩
    · intro n ⟨hT, hF⟩
      change v n = BoolVal.T at hT
      change v n = BoolVal.F at hF
      rw [hT] at hF; exact absurd hF (by decide)
    · intro a ha
      cases a with
      | tConj X Y =>
        have hEval : evalExtN v (.conj X Y) = BoolVal.T := ha
        simp only [evalExtN, hAnd] at hEval
        constructor
        · show evalExtN v X = BoolVal.T
          cases hx : evalExtN v X <;> cases hy : evalExtN v Y <;> simp_all [hAnd]
        · show evalExtN v Y = BoolVal.T
          cases hx : evalExtN v X <;> cases hy : evalExtN v Y <;> simp_all [hAnd]
      | fDisj X Y =>
        have hEval : evalExtN v (.disj X Y) = BoolVal.F := ha
        simp only [evalExtN, hOr] at hEval
        constructor
        · show evalExtN v X = BoolVal.F
          cases hx : evalExtN v X <;> cases hy : evalExtN v Y <;> simp_all [hOr]
        · show evalExtN v Y = BoolVal.F
          cases hx : evalExtN v X <;> cases hy : evalExtN v Y <;> simp_all [hOr]
      | fImpl X Y =>
        have hEval : evalExtN v (.impl X Y) = BoolVal.F := ha
        simp only [evalExtN, hImplies] at hEval
        constructor
        · show evalExtN v X = BoolVal.T
          cases hx : evalExtN v X <;> cases hy : evalExtN v Y <;> simp_all [hImplies]
        · show evalExtN v Y = BoolVal.F
          cases hx : evalExtN v X <;> cases hy : evalExtN v Y <;> simp_all [hImplies]
      | tNeg X =>
        have hEval : evalExtN v (.neg X) = BoolVal.T := ha
        simp only [evalExtN, hNeg] at hEval
        have hXF : evalExtN v X = BoolVal.F := by
          cases hx : evalExtN v X <;> simp_all [hNeg]
        exact ⟨hXF, hXF⟩
      | fNeg X =>
        have hEval : evalExtN v (.neg X) = BoolVal.F := ha
        simp only [evalExtN, hNeg] at hEval
        have hXT : evalExtN v X = BoolVal.T := by
          cases hx : evalExtN v X <;> simp_all [hNeg]
        exact ⟨hXT, hXT⟩
    · intro b hb
      cases b with
      | fConj X Y =>
        have hEval : evalExtN v (.conj X Y) = BoolVal.F := hb
        simp only [evalExtN, hAnd] at hEval
        show evalExtN v X = BoolVal.F ∨ evalExtN v Y = BoolVal.F
        cases hx : evalExtN v X <;> cases hy : evalExtN v Y <;> simp_all [hAnd]
      | tDisj X Y =>
        have hEval : evalExtN v (.disj X Y) = BoolVal.T := hb
        simp only [evalExtN, hOr] at hEval
        show evalExtN v X = BoolVal.T ∨ evalExtN v Y = BoolVal.T
        cases hx : evalExtN v X <;> cases hy : evalExtN v Y <;> simp_all [hOr]
      | tImpl X Y =>
        have hEval : evalExtN v (.impl X Y) = BoolVal.T := hb
        simp only [evalExtN, hImplies] at hEval
        show evalExtN v X = BoolVal.F ∨ evalExtN v Y = BoolVal.T
        cases hx : evalExtN v X <;> cases hy : evalExtN v Y <;> simp_all [hImplies]
  case sat =>
    intro sf hsf
    cases sf with
    | trueF A => exact hsf
    | falseF A => exact hsf

helper /-- Theorem 3.5.1 (infrastructure for future proving): Finite sequent case
    of the falsifiable branch. If a finite sequent is falsifiable, a Hintikka
    set and falsifying valuation exist (reduces to the infinite case). Like
    `infinite_sequent_falsifiable_case` above, this is a semantic-only
    companion that bypasses `infSearch`. -/
theorem finite_sequent_falsifiable_case (seq : InfSequent)
    (hFinAnt : ∃ N, ∀ n, n ≥ N → seq.antecedent n = none)
    (hFinSuc : ∃ M, ∀ n, n ≥ M → seq.succedent n = none)
    (hFals : infSeqFalsifiable seq)
    : ∃ (S : Set SignedFormula), IsHintikkaSet S ∧
      (∃ v : Valuation, SignedSet.satisfiedBy S v ∧ infSeqFalsifies v seq) :=
-- BEGIN PROOF
  infinite_sequent_falsifiable_case seq hFals

helper /-- Theorem 3.5.1 (infrastructure for future proving): If an infinite
    sequent is not valid, a falsifying valuation exists via classical
    extraction. This bypasses `infSearch` — the main textbook statement
    `search_theorem_3_5_1` obtains the falsifying valuation from a
    `infSearchSteps`-produced search tree path. -/
theorem falsifying_valuation_from_path (seq : InfSequent)
    (h : ¬infSeqValid seq)
    : ∃ v : Valuation, infSeqFalsifies v seq :=
-- BEGIN PROOF
by
  unfold infSeqValid at h
  have ⟨v, hv⟩ := Classical.not_forall.mp h
  unfold infSeqSatisfies at hv
  have hv' := Classical.not_imp.mp hv
  obtain ⟨hAnt, hSuc⟩ := hv'
  refine ⟨v, hAnt, fun n B hn => ?_⟩
  cases hb : evalExtN v B with
  | F => rfl
  | T => exact absurd ⟨n, B, hn, hb⟩ hSuc

helper /-- Every finite traversal contains its actual root, including an empty choice list. -/
theorem root_mem_sequentsAlongPath {s : Sequent} (dt : DeductionTree s) (p : Path) :
    s ∈ sequentsAlongPath dt p := by
  cases dt with
  | leaf => simp [sequentsAlongPath]
  | onePremise => exact List.Mem.head _
  | twoPremise => cases p with
    | nil => exact List.Mem.head _
    | cons d p => cases d <;> exact List.Mem.head _

helper theorem pathSignedSet_iff {s : Sequent} (dt : DeductionTree s) (p : Path)
    (sf : SignedFormula) :
    pathSignedSet dt p sf ↔ ∃ t ∈ sequentsAlongPath dt p, occurs t sf := by
  cases sf <;> rfl

helper /-- Following a finite branch either preserves a formula to its endpoint,
    or witnesses its decomposition somewhere on that same branch. -/
theorem path_support_from_root {s : Sequent} (dt : DeductionTree s) (p : Path)
    (hwf : WFTree dt) (sf : SignedFormula) (h : occurs s sf) :
    occurs (leafSeq dt p) sf ∨ expanded (pathSignedSet dt p) sf := by
  induction hwf generalizing p with
  | leaf s => exact Or.inl h
  | @step1 prem conc child rule hchild ih =>
    have hsub : ∀ sf, pathSignedSet child p sf →
        pathSignedSet (.onePremise rule child) p sf := by
      intro sf hsf
      rw [pathSignedSet_iff] at hsf ⊢
      obtain ⟨t, ht, hm⟩ := hsf
      exact ⟨t, List.Mem.tail _ ht, hm⟩
    have hend : leafSeq (.onePremise rule child) p = leafSeq child p := by
      simp only [leafSeq, sequentsAlongPath, List.getLast_cons (sequentsAlongPath_ne_nil _ _)]
    rw [hend]
    rcases step1_support rule sf h with hp | he
    · exact support_lift hsub (ih p hp)
    · exact Or.inr (expanded_mono (fun sf hm => hsub sf
        ((pathSignedSet_iff child p sf).mpr
          ⟨prem, root_mem_sequentsAlongPath child p, hm⟩)) sf he)
  | @step2 p1 p2 conc c1 c2 rule hw1 hw2 ih1 ih2 =>
    cases p with
    | nil => exact Or.inl h
    | cons dir rest =>
      cases dir with
      | left =>
        have hsub : ∀ sf, pathSignedSet c1 rest sf →
            pathSignedSet (.twoPremise rule c1 c2) (.left :: rest) sf := by
          intro sf hsf
          rw [pathSignedSet_iff] at hsf ⊢
          obtain ⟨t, ht, hm⟩ := hsf
          exact ⟨t, List.Mem.tail _ ht, hm⟩
        have hend : leafSeq (.twoPremise rule c1 c2) (.left :: rest) =
            leafSeq c1 rest := by
          simp only [leafSeq, sequentsAlongPath, List.getLast_cons (sequentsAlongPath_ne_nil _ _)]
        rw [hend]
        rcases step2_support_left rule sf h with hp | he
        · exact support_lift hsub (ih1 rest hp)
        · exact Or.inr (expanded_mono (fun sf hm => hsub sf
            ((pathSignedSet_iff c1 rest sf).mpr
              ⟨p1, root_mem_sequentsAlongPath c1 rest, hm⟩)) sf he)
      | right =>
        have hsub : ∀ sf, pathSignedSet c2 rest sf →
            pathSignedSet (.twoPremise rule c1 c2) (.right :: rest) sf := by
          intro sf hsf
          rw [pathSignedSet_iff] at hsf ⊢
          obtain ⟨t, ht, hm⟩ := hsf
          exact ⟨t, List.Mem.tail _ ht, hm⟩
        have hend : leafSeq (.twoPremise rule c1 c2) (.right :: rest) =
            leafSeq c2 rest := by
          simp only [leafSeq, sequentsAlongPath, List.getLast_cons (sequentsAlongPath_ne_nil _ _)]
        rw [hend]
        rcases step2_support_right rule sf h with hp | he
        · exact support_lift hsub (ih2 rest hp)
        · exact Or.inr (expanded_mono (fun sf hm => hsub sf
            ((pathSignedSet_iff c2 rest sf).mpr
              ⟨p2, root_mem_sequentsAlongPath c2 rest, hm⟩)) sf he)

helper theorem path_support {s : Sequent} (dt : DeductionTree s) (p : Path)
    (hwf : WFTree dt) (sf : SignedFormula) (h : pathSignedSet dt p sf) :
    occurs (leafSeq dt p) sf ∨ expanded (pathSignedSet dt p) sf := by
  induction hwf generalizing p with
  | leaf s =>
    rw [pathSignedSet_iff] at h
    exact Or.inl (by simpa [leafSeq, sequentsAlongPath] using h)
  | @step1 prem conc child rule hchild ih =>
    rw [pathSignedSet_iff] at h
    obtain ⟨t, ht, hm⟩ := h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact path_support_from_root _ p (.step1 rule hchild) sf hm
    · have hsub : ∀ sf, pathSignedSet child p sf →
          pathSignedSet (.onePremise rule child) p sf := by
        intro sf hsf
        rw [pathSignedSet_iff] at hsf ⊢
        obtain ⟨t, ht, hm⟩ := hsf
        exact ⟨t, List.Mem.tail _ ht, hm⟩
      have hr := support_lift hsub (ih p ((pathSignedSet_iff child p sf).mpr ⟨t, ht, hm⟩))
      simpa only [leafSeq, sequentsAlongPath, List.getLast_cons (sequentsAlongPath_ne_nil _ _)] using hr
  | @step2 p1 p2 conc c1 c2 rule hw1 hw2 ih1 ih2 =>
    cases p with
    | nil =>
      rw [pathSignedSet_iff] at h
      exact Or.inl (by simpa [leafSeq, sequentsAlongPath] using h)
    | cons dir rest =>
      cases dir with
      | left =>
        rw [pathSignedSet_iff] at h
        obtain ⟨t, ht, hm⟩ := h
        rcases List.mem_cons.mp ht with rfl | ht
        · exact path_support_from_root _ _ (.step2 rule hw1 hw2) sf hm
        · have hsub : ∀ sf, pathSignedSet c1 rest sf →
              pathSignedSet (.twoPremise rule c1 c2) (.left :: rest) sf := by
            intro sf hsf
            rw [pathSignedSet_iff] at hsf ⊢
            obtain ⟨t, ht, hm⟩ := hsf
            exact ⟨t, List.Mem.tail _ ht, hm⟩
          have hr := support_lift hsub (ih1 rest ((pathSignedSet_iff c1 rest sf).mpr ⟨t, ht, hm⟩))
          simpa only [leafSeq, sequentsAlongPath, List.getLast_cons (sequentsAlongPath_ne_nil _ _)] using hr
      | right =>
        rw [pathSignedSet_iff] at h
        obtain ⟨t, ht, hm⟩ := h
        rcases List.mem_cons.mp ht with rfl | ht
        · exact path_support_from_root _ _ (.step2 rule hw1 hw2) sf hm
        · have hsub : ∀ sf, pathSignedSet c2 rest sf →
              pathSignedSet (.twoPremise rule c1 c2) (.right :: rest) sf := by
            intro sf hsf
            rw [pathSignedSet_iff] at hsf ⊢
            obtain ⟨t, ht, hm⟩ := hsf
            exact ⟨t, List.Mem.tail _ ht, hm⟩
          have hr := support_lift hsub (ih2 rest ((pathSignedSet_iff c2 rest sf).mpr ⟨t, ht, hm⟩))
          simpa only [leafSeq, sequentsAlongPath, List.getLast_cons (sequentsAlongPath_ne_nil _ _)] using hr

helper theorem hintikka_of_support (S : Set SignedFormula) (terminal : Sequent)
    (hsupport : ∀ sf, S sf → occurs terminal sf ∨ expanded S sf)
    (hna : ¬isAxiom terminal)
    (hAnt : ∀ A ∈ terminal.antecedent, isAtomicFormula A)
    (hSuc : ∀ A ∈ terminal.succedent, isAtomicFormula A) : IsHintikkaSet S := by
  constructor
  · intro n ⟨ht, hf⟩
    have ht := hsupport (.trueF (.var n)) ht
    have hf := hsupport (.falseF (.var n)) hf
    simp only [expanded, or_false, occurs] at ht hf
    exact hna ⟨.var n, ht, hf⟩
  · intro a ha
    change S a.comp1 ∧ S a.comp2
    have h := hsupport a.toSigned ha
    cases a <;> simp_all [TypeA.toSigned, TypeA.comp1, TypeA.comp2, expanded, occurs,
      isAtomicFormula] <;> grind
  · intro b hb
    change S b.comp1 ∨ S b.comp2
    have h := hsupport b.toSigned hb
    cases b <;> simp_all [TypeB.toSigned, TypeB.comp1, TypeB.comp2, expanded, occurs,
      isAtomicFormula] <;> grind

proof_of finite_hintikka_set_extraction := hintikka_of_support _ _ (path_support dt p hwf) hna hAnt hSuc


helper theorem branchPrincipal_expanded {s t : Sequent} (step : InfBranchStep s t)
    (sf : SignedFormula) (h : branchPrincipal step = some sf) :
    expanded (occurs t) sf := by
  cases step with
  | onePremise r =>
    cases r <;> simp only [branchPrincipal, principal1, Option.some.injEq] at h <;>
      subst sf <;> simp [expanded, occurs]
  | leftPremise r =>
    cases r <;> simp only [branchPrincipal, principal2, Option.some.injEq] at h <;>
      subst sf <;> simp [expanded, occurs]
  | rightPremise r =>
    cases r <;> simp only [branchPrincipal, principal2, Option.some.injEq] at h <;>
      subst sf <;> simp [expanded, occurs]
  | extend => simp [branchPrincipal] at h
  | idle => simp [branchPrincipal] at h

helper /-- A rule can remove an occurrence only when that formula is its principal. -/
theorem branchStep_persist_or_selected {s t : Sequent} (step : InfBranchStep s t)
    (sf : SignedFormula) (h : occurs s sf) :
    occurs t sf ∨ branchPrincipal step = some sf := by
  cases step with
  | onePremise r =>
    cases r <;> cases sf <;> simp_all [occurs, branchPrincipal, principal1] <;> grind
  | leftPremise r =>
    cases r <;> cases sf <;> simp_all [occurs, branchPrincipal, principal2] <;> grind
  | rightPremise r =>
    cases r <;> cases sf <;> simp_all [occurs, branchPrincipal, principal2] <;> grind
  | extend a b =>
    apply Or.inl
    cases sf <;> simp_all [occurs, extendSeq]
  | idle => exact Or.inl h

helper /-- Track an occurrence to a later point of a branch, retaining the exact
    intervening principal event if the occurrence disappears. -/
theorem branch_occurrence_until (label : Nat → Sequent)
    (steps : ∀ n, InfBranchStep (label n) (label (n + 1)))
    (i j : Nat) (hij : i ≤ j) (sf : SignedFormula) (hi : occurs (label i) sf) :
    occurs (label j) sf ∨
      ∃ m, i ≤ m ∧ m < j ∧ branchPrincipal (steps m) = some sf := by
  induction hij with
  | refl => exact Or.inl hi
  | @step j hij ih =>
    rcases ih with h | ⟨m, him, hmj, hm⟩
    · rcases branchStep_persist_or_selected (steps j) sf h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨j, hij, Nat.lt_succ_self j, h⟩
    · exact Or.inr ⟨m, him, Nat.lt_trans hmj (Nat.lt_succ_self j), hm⟩

helper /-- Translate the finite search's side-tagged principal (`true` = succedent). -/
def signedPrincipal (p : Bool × PropFormulaNormalized) : SignedFormula :=
  if p.1 then .falseF p.2 else .trueF p.2

helper /-- An addressed finite-search rule is a genuine signed decomposition event. -/
theorem ruleEdgeAt_signed {s : Sequent} {tree : DeductionTree s}
    {address dir parent child principal}
    (h : RuleEdgeAt tree address dir parent child principal) :
    ∃ selected : InfBranchStep parent child,
      branchPrincipal selected = some (signedPrincipal principal) := by
  induction h with
  | rootOne r tree =>
    refine ⟨.onePremise r, ?_⟩
    cases r <;> rfl
  | rootLeft r l rgt =>
    refine ⟨.leftPremise r, ?_⟩
    cases r <;> rfl
  | rootRight r l rgt =>
    refine ⟨.rightPremise r, ?_⟩
    cases r <;> rfl
  | down h ih => exact ih
  | left h ih => exact ih
  | right h ih => exact ih

helper /-- Both labels of that event occur at its exact embedded tree addresses. -/
theorem ruleEdgeAt_labels {s : Sequent} {tree : DeductionTree s}
    {address dir parent child principal}
    (h : RuleEdgeAt tree address dir parent child principal) :
    (InfDeductionTree.ofDeductionTree tree).labelAt address = some parent ∧
    (InfDeductionTree.ofDeductionTree tree).labelAt (address ++ [dir]) = some child := by
  induction h with
  | rootOne => simp [InfDeductionTree.ofDeductionTree, InfDeductionTree.labelAt]
  | rootLeft => simp [InfDeductionTree.ofDeductionTree, InfDeductionTree.labelAt]
  | rootRight => simp [InfDeductionTree.ofDeductionTree, InfDeductionTree.labelAt]
  | down h ih => simpa [InfDeductionTree.ofDeductionTree, InfDeductionTree.labelAt] using ih
  | left h ih => simpa [InfDeductionTree.ofDeductionTree, InfDeductionTree.labelAt] using ih
  | right h ih => simpa [InfDeductionTree.ofDeductionTree, InfDeductionTree.labelAt] using ih

helper /-- Every original compound is selected on each open branch of one complete
    systematic expansion. The witness records the actual edge and both labels. -/
theorem expandLeaf_signed_event {s terminal address ps side A}
    (h : AddressedLeafPath (expandLeaf .systematic s) address terminal ps)
    (ho : ¬isAxiom terminal)
    (hm : A ∈ if side then s.succedent else s.antecedent)
    (hn : isNonatomicFormula A) :
    ∃ edgeAddress dir parent child,
      (InfDeductionTree.ofDeductionTree (expandLeaf .systematic s)).labelAt edgeAddress =
        some parent ∧
      (InfDeductionTree.ofDeductionTree (expandLeaf .systematic s)).labelAt
        (edgeAddress ++ [dir]) = some child ∧
      (edgeAddress ++ [dir]).IsPrefix address ∧
      ∃ selected : InfBranchStep parent child,
        branchPrincipal selected = some (signedPrincipal (side, A)) := by
  obtain ⟨q, d, parent, child, he, hp⟩ := expandLeaf_addressed_fair h ho hm hn
  exact ⟨q, d, parent, child, (ruleEdgeAt_labels he).1, (ruleEdgeAt_labels he).2,
    hp, ruleEdgeAt_signed he⟩

helper /-- Recover the finite algorithm's exact addressed path from a leaf lookup
    in its embedding into an infinite-search stage. -/
theorem addressedLeafPath_of_leafAt {s : Sequent} (tree : DeductionTree s)
    (address : List Nat) (terminal : Sequent)
    (h : (InfDeductionTree.ofDeductionTree tree).leafAt address = some terminal) :
    ∃ ps, AddressedLeafPath tree address terminal ps := by
  induction tree generalizing address terminal with
  | leaf s =>
    cases address with
    | nil =>
      simp only [InfDeductionTree.ofDeductionTree, InfDeductionTree.leafAt,
        Option.some.injEq] at h
      subst terminal
      exact ⟨[], .leaf s⟩
    | cons => simp [InfDeductionTree.ofDeductionTree, InfDeductionTree.leafAt] at h
  | onePremise r tree ih =>
    cases address with
    | nil => simp [InfDeductionTree.ofDeductionTree, InfDeductionTree.leafAt] at h
    | cons dir rest =>
      cases dir with
      | zero =>
        obtain ⟨ps, hp⟩ := ih rest terminal h
        exact ⟨_, .down hp⟩
      | succ => simp [InfDeductionTree.ofDeductionTree, InfDeductionTree.leafAt] at h
  | twoPremise r l rgt ihl ihr =>
    cases address with
    | nil => simp [InfDeductionTree.ofDeductionTree, InfDeductionTree.leafAt] at h
    | cons dir rest =>
      cases dir with
      | zero =>
        obtain ⟨ps, hp⟩ := ihl rest terminal h
        exact ⟨_, .left hp⟩
      | succ dir =>
        cases dir with
        | zero =>
          obtain ⟨ps, hp⟩ := ihr rest terminal h
          exact ⟨_, .right hp⟩
        | succ => simp [InfDeductionTree.ofDeductionTree, InfDeductionTree.leafAt] at h

proof_of finished_search_hintikka_set_extraction := by
  have ⟨leaf, hleaf, hopen⟩ : ∃ leaf ∈ (infSearchSteps seq k).tree.leaves, ¬isAxiom leaf := by
    simpa using hopen
  obtain ⟨labels, hp⟩ := SearchTreePath.exists_of_leaf _ leaf hleaf
  have hatomic := (hfinished leaf hleaf).resolve_left hopen
  refine ⟨leaf, labels, hp, hintikka_of_support _ leaf (hp.support) hopen ?_ ?_⟩
  · intro A hA
    exact hatomic.2.2 A (List.mem_append_left _ hA)
  · intro A hA
    exact hatomic.2.2 A (List.mem_append_right _ hA)


helper /-- Extract all labels and genuine rule/introduction edges of an infinite
    path in the actual search limit. -/
theorem infinite_limit_path_labels (seq : InfSequent) (address : Nat → List Nat)
    (hpath : (infSearchTreeDomain seq).InfinitePath address) :
    ∃ label : Nat → Sequent,
      (∀ n, infSearchLimit seq (address n) (label n)) ∧
      (∀ n, Nonempty (InfBranchStep (label n) (label (n + 1)))) := by
  have hnodes : ∀ n, ∃ s, infSearchLimit seq (address n) s := by
    intro n
    cases n with
    | zero =>
      rw [hpath.1]
      exact ⟨(infSearchInit seq).rootSeq, 0, rfl⟩
    | succ n => exact (hpath.2 n).2
  let label := fun n => Classical.choose (hnodes n)
  have hlabel n : infSearchLimit seq (address n) (label n) :=
    Classical.choose_spec (hnodes n)
  refine ⟨label, hlabel, ?_⟩
  intro n
  rcases (hpath.2 n).1 with h | h
  · exact LCS.Propositional.Infinite.Proofs.infSearchLimit_branchStep seq (address n) 0 (hlabel n)
      (by simpa only [h] using hlabel (n + 1))
  · exact LCS.Propositional.Infinite.Proofs.infSearchLimit_branchStep seq (address n) 1 (hlabel n)
      (by simpa only [h] using hlabel (n + 1))

helper /-- Every finite prefix of a limit path is the path node at its own length. -/
theorem search_path_prefix_eq (seq : InfSequent) (address : Nat → List Nat)
    (hp : (infSearchTreeDomain seq).InfinitePath address) {q : List Nat} {n : Nat}
    (hq : q.IsPrefix (address n)) : q = address q.length := by
  obtain ⟨suffix, heq⟩ := hq
  have hlen : q.length ≤ n := by
    have h := congrArg List.length heq
    rw [List.length_append, LCS.Propositional.Infinite.Proofs.infSearchPath_length seq address hp n] at h
    omega
  have h := congrArg (List.take q.length) heq
  simpa [LCS.Propositional.Infinite.Proofs.infSearchPath_take seq address hp q.length n hlen] using h

helper /-- A selected rule at an actual limit-tree edge lying between two nodes of
    the chosen path supplies the corresponding temporal fairness event. -/
theorem limit_principal_event_on_path (seq : InfSequent) (address : Nat → List Nat)
    (label : Nat → Sequent) (hp : (infSearchTreeDomain seq).InfinitePath address)
    (hl : ∀ n, infSearchLimit seq (address n) (label n))
    {i endpoint : Nat} {q : List Nat} {dir : Nat} {parent child : Sequent}
    {sf : SignedFormula} (hstart : (address i).IsPrefix q)
    (hend : (q ++ [dir]).IsPrefix (address endpoint))
    (hparent : infSearchLimit seq q parent)
    (hchild : infSearchLimit seq (q ++ [dir]) child)
    (hselected : ∃ selected : InfBranchStep parent child,
      branchPrincipal selected = some sf) :
    ∃ m, i ≤ m ∧ ∃ selected : InfBranchStep (label m) (label (m + 1)),
      branchPrincipal selected = some sf := by
  have hqprefix : q.IsPrefix (address endpoint) := by
    obtain ⟨suffix, hs⟩ := hend
    exact ⟨[dir] ++ suffix, by simpa [List.append_assoc] using hs⟩
  have hq := search_path_prefix_eq seq address hp hqprefix
  have hqd := search_path_prefix_eq seq address hp hend
  have hlen : i ≤ q.length := by
    obtain ⟨suffix, hs⟩ := hstart
    have h := congrArg List.length hs
    rw [List.length_append, LCS.Propositional.Infinite.Proofs.infSearchPath_length seq address hp i] at h
    omega
  have hparent' : infSearchLimit seq (address q.length) parent := by
    rw [← hq]
    exact hparent
  have hparent_eq : parent = label q.length :=
    LCS.Propositional.Infinite.Proofs.infSearchLimit_unique seq (address q.length) parent (label q.length) hparent' (hl q.length)
  have hqd' : q ++ [dir] = address (q.length + 1) := by simpa using hqd
  have hchild' : infSearchLimit seq (address (q.length + 1)) child := by
    rw [← hqd']
    exact hchild
  have hchild_eq : child = label (q.length + 1) :=
    LCS.Propositional.Infinite.Proofs.infSearchLimit_unique seq (address (q.length + 1)) child (label (q.length + 1))
      hchild' (hl (q.length + 1))
  subst parent
  subst child
  exact ⟨q.length, hlen, hselected⟩

helper /-- The segment of an infinite limit path through one unfinished stage leaf
    traverses that leaf's actual systematic expansion and then introduces
    the two scheduled heads. All old expansion labels remain in the limit. -/
theorem next_stage_expansion_path (seq : InfSequent) (address : Nat → List Nat)
    (label : Nat → Sequent) (hp : (infSearchTreeDomain seq).InfinitePath address)
    (hl : ∀ n, infSearchLimit seq (address n) (label n)) (k n : Nat)
    (hleaf : (infSearchSteps seq k).tree.leafAt (address n) = some (label n))
    (hunfinished : infIsFinishedLeafBool (infSearchSteps seq k) (label n) = false) :
    ∃ m q terminal ps, n ≤ m ∧ address m = address n ++ (q ++ [0]) ∧
      AddressedLeafPath (expandLeaf .systematic (label n)) q terminal ps ∧
      ¬isAxiom terminal ∧
      label m = extendSeq terminal (InfSeq.head (infSearchSteps seq k).L)
        (InfSeq.head (infSearchSteps seq k).R) ∧
      (∀ p s, (InfDeductionTree.ofDeductionTree (expandLeaf .systematic (label n))).labelAt p =
        some s → infSearchLimit seq (address n ++ p) s) := by
  let st := infSearchSteps seq k
  let replace (s : Sequent) : InfDeductionTree s :=
    if infIsFinishedLeafBool st s then .leaf s
    else appendToLeavesCore (InfDeductionTree.ofDeductionTree (expandLeaf .systematic s))
      (InfSeq.head st.L) (InfSeq.head st.R)
  let addHeads (s : Sequent) : InfDeductionTree s :=
    if isAxiomBool s then .leaf s
    else .extend (InfSeq.head st.L) (InfSeq.head st.R)
      (.leaf (extendSeq s (InfSeq.head st.L) (InfSeq.head st.R)))
  obtain ⟨m, hm⟩ := LCS.Propositional.Infinite.Proofs.infSearchPath_crosses_stage_leaf seq address label hp hl (k + 1)
  have hnnode : (infSearchSteps seq (k + 1)).tree.labelAt (address n) = some (label n) :=
    LCS.Propositional.Infinite.Proofs.infExpand_labelAt_preserves st _ _ (InfDeductionTree.labelAt_of_leafAt _ _ hleaf)
  have hnm := LCS.Propositional.Infinite.Proofs.infSearchPath_node_before_leaf seq address hp (k + 1) n m _ _ hnnode hm
  let suffix := (address m).drop n
  have hsplit : address m = address n ++ suffix := by
    calc
      address m = (address m).take n ++ (address m).drop n := (List.take_append_drop _ _).symm
      _ = address n ++ suffix := by rw [LCS.Propositional.Infinite.Proofs.infSearchPath_take seq address hp n m hnm]
  have hlocal : (replace (label n)).leafAt suffix = some (label m) := by
    rw [← InfDeductionTree.leafAt_bindLeaves_below_leaf replace st.tree (address n) suffix hleaf]
    change (infSearchSteps seq (k + 1)).tree.leafAt (address n ++ suffix) = some (label m)
    rw [← hsplit]
    exact hm
  have hlocal' : ((InfDeductionTree.ofDeductionTree (expandLeaf .systematic (label n))).bindLeaves
      addHeads).leafAt suffix = some (label m) := by
    simpa only [replace, hunfinished, Bool.false_eq_true, ↓reduceIte, appendToLeavesCore, st]
      using hlocal
  obtain ⟨q, tail, terminal, hq, hterminal, hafter⟩ :=
    InfDeductionTree.leafAt_bindLeaves_decompose addHeads _ suffix hlocal'
  have hopen : ¬isAxiom terminal := by
    intro ha
    have hb : isAxiomBool terminal = true := (LCS.Propositional.Infinite.Proofs.isAxiomBool_iff terminal).mpr ha
    simp only [addHeads, hb, ↓reduceIte] at hafter
    cases tail with
    | nil =>
      have heq : terminal = label m := Option.some.inj hafter
      exact LCS.Propositional.Infinite.Proofs.infSearchPath_nonaxiom seq address label hp hl m (heq ▸ ha)
    | cons => simp [InfDeductionTree.leafAt] at hafter
  have hb : isAxiomBool terminal = false := by
    cases h : isAxiomBool terminal with
    | false => rfl
    | true => exact False.elim (hopen ((LCS.Propositional.Infinite.Proofs.isAxiomBool_iff terminal).mp h))
  have htail : tail = [0] ∧ label m = extendSeq terminal (InfSeq.head st.L) (InfSeq.head st.R) := by
    simp only [addHeads, hb, Bool.false_eq_true, ↓reduceIte] at hafter
    cases tail with
    | nil => simp [InfDeductionTree.leafAt] at hafter
    | cons dir rest =>
      cases dir with
      | succ => simp [InfDeductionTree.leafAt] at hafter
      | zero =>
        cases rest with
        | nil => exact ⟨rfl, (Option.some.inj hafter).symm⟩
        | cons => simp [InfDeductionTree.leafAt] at hafter
  obtain ⟨ps, hpath⟩ := addressedLeafPath_of_leafAt _ q terminal hterminal
  refine ⟨m, q, terminal, ps, hnm, ?_, hpath, hopen, htail.2, ?_⟩
  · rw [hsplit, hq, htail.1]
  · intro p s hs
    refine ⟨k + 1, ?_⟩
    change (st.tree.bindLeaves replace).labelAt (address n ++ p) = some s
    rw [InfDeductionTree.labelAt_bindLeaves_below_leaf replace st.tree (address n) p hleaf]
    simp only [replace, show infIsFinishedLeafBool st (label n) = false from hunfinished,
      Bool.false_eq_true, ↓reduceIte]
    exact InfDeductionTree.labelAt_bindLeaves_preserves addHeads _ p s hs

helper theorem unfinished_of_compound (st : InfSearchState) (s : Sequent)
    (ho : ¬isAxiom s) (sf : SignedFormula) (hm : occurs s sf)
    (hc : sf.classify ≠ none) : infIsFinishedLeafBool st s = false := by
  cases h : infIsFinishedLeafBool st s with
  | false => rfl
  | true =>
    rcases (LCS.Propositional.Infinite.Proofs.infIsFinishedLeafBool_iff st s).mp h with hax | ⟨_, _, hatomic⟩
    · exact False.elim (ho hax)
    · cases sf with
      | trueF A =>
        have ha := hatomic A (List.mem_append_left _ hm)
        cases A <;> simp_all [SignedFormula.classify, isAtomicFormula]
      | falseF A =>
        have ha := hatomic A (List.mem_append_right _ hm)
        cases A <;> simp_all [SignedFormula.classify, isAtomicFormula]

helper /-- A compound at an actual stage leaf is selected later on the same
    infinite path by that leaf's next systematic expansion. -/
theorem stage_leaf_principal_event (seq : InfSequent) (address : Nat → List Nat)
    (label : Nat → Sequent) (hp : (infSearchTreeDomain seq).InfinitePath address)
    (hl : ∀ n, infSearchLimit seq (address n) (label n)) (k n : Nat)
    (hleaf : (infSearchSteps seq k).tree.leafAt (address n) = some (label n))
    (sf : SignedFormula) (hm : occurs (label n) sf) (hc : sf.classify ≠ none) :
    ∃ m, n ≤ m ∧ ∃ selected : InfBranchStep (label m) (label (m + 1)),
      branchPrincipal selected = some sf := by
  have huf := unfinished_of_compound (infSearchSteps seq k) (label n)
    (LCS.Propositional.Infinite.Proofs.infSearchPath_nonaxiom seq address label hp hl n) sf hm hc
  obtain ⟨endpoint, q, terminal, ps, _, hend, hfinite, hopen, _, hlift⟩ :=
    next_stage_expansion_path seq address label hp hl k n hleaf huf
  have hevent : ∃ r dir parent child,
      (InfDeductionTree.ofDeductionTree (expandLeaf .systematic (label n))).labelAt r = some parent ∧
      (InfDeductionTree.ofDeductionTree (expandLeaf .systematic (label n))).labelAt
        (r ++ [dir]) = some child ∧
      (r ++ [dir]).IsPrefix q ∧
      ∃ selected : InfBranchStep parent child, branchPrincipal selected = some sf := by
    cases sf with
    | trueF A =>
      have hn : isNonatomicFormula A := by cases A <;> simp_all [SignedFormula.classify, isNonatomicFormula]
      simpa [signedPrincipal] using
        (expandLeaf_signed_event (side := false) hfinite hopen hm hn)
    | falseF A =>
      have hn : isNonatomicFormula A := by cases A <;> simp_all [SignedFormula.classify, isNonatomicFormula]
      simpa [signedPrincipal] using
        (expandLeaf_signed_event (side := true) hfinite hopen hm hn)
  obtain ⟨r, dir, parent, child, hr, hrc, hprefix, hselected⟩ := hevent
  apply limit_principal_event_on_path seq address label hp hl
    (i := n) (endpoint := endpoint) (q := address n ++ r) (dir := dir)
    (parent := parent) (child := child) (sf := sf)
  · exact ⟨r, rfl⟩
  · obtain ⟨suffix, hq⟩ := hprefix
    refine ⟨suffix ++ [0], ?_⟩
    rw [hend, ← hq]
    simp only [List.append_assoc]
  · exact hlift r parent hr
  · simpa only [List.append_assoc] using hlift (r ++ [dir]) child hrc
  · exact hselected

helper /-- Fairness for every occurrence on an actual infinite search-limit path.
    This is derived from finite stages and the procedure's frozen schedule. -/
theorem infinite_limit_path_fair (seq : InfSequent) (address : Nat → List Nat)
    (label : Nat → Sequent) (hp : (infSearchTreeDomain seq).InfinitePath address)
    (hl : ∀ n, infSearchLimit seq (address n) (label n))
    (steps : ∀ n, InfBranchStep (label n) (label (n + 1))) :
    ∀ i sf, occurs (label i) sf → sf.classify ≠ none →
      ∃ m, i ≤ m ∧ ∃ selected : InfBranchStep (label m) (label (m + 1)),
        branchPrincipal selected = some sf := by
  intro i sf hm hc
  obtain ⟨k, hnode⟩ := hl i
  obtain ⟨n, hleaf⟩ := LCS.Propositional.Infinite.Proofs.infSearchPath_crosses_stage_leaf seq address label hp hl k
  have hin := LCS.Propositional.Infinite.Proofs.infSearchPath_node_before_leaf seq address hp k i n _ _ hnode hleaf
  rcases branch_occurrence_until label steps i n hin sf hm with hn | ⟨m, him, _, he⟩
  · obtain ⟨m, hnm, selected, he⟩ := stage_leaf_principal_event seq address label hp hl k n hleaf sf hn hc
    exact ⟨m, Nat.le_trans hin hnm, selected, he⟩
  · exact ⟨m, him, steps m, he⟩

helper theorem unfinished_of_head (st : InfSearchState) (s : Sequent)
    (ho : ¬isAxiom s)
    (hhead : InfSeq.head st.L ≠ none ∨ InfSeq.head st.R ≠ none) :
    infIsFinishedLeafBool st s = false := by
  cases h : infIsFinishedLeafBool st s with
  | false => rfl
  | true =>
    rcases (LCS.Propositional.Infinite.Proofs.infIsFinishedLeafBool_iff st s).mp h with hax | ⟨hL, hR, _⟩
    · exact False.elim (ho hax)
    · rcases hhead with hhead | hhead
      · exact False.elim (hhead (hL 0))
      · exact False.elim (hhead (hR 0))

helper /-- Every enumerated input formula really enters each infinite limit path.
    Index zero is at the root; index k+1 is introduced in round k+1. -/
theorem infinite_limit_path_covers_input (seq : InfSequent) (address : Nat → List Nat)
    (label : Nat → Sequent) (hp : (infSearchTreeDomain seq).InfinitePath address)
    (hl : ∀ n, infSearchLimit seq (address n) (label n)) :
    ∀ sf, signedSetOfSequent seq sf → ∃ n, occurs (label n) sf := by
  have hroot : label 0 = (infSearchInit seq).rootSeq := by
    apply LCS.Propositional.Infinite.Proofs.infSearchLimit_unique seq (address 0) _ _ (hl 0)
    rw [hp.1]
    exact ⟨0, rfl⟩
  intro sf hs
  cases sf with
  | trueF A =>
    obtain ⟨index, hindex⟩ := hs
    cases index with
    | zero =>
      refine ⟨0, ?_⟩
      rw [hroot]
      simp [occurs, infSearchInit, InfSeq.head, hindex]
    | succ k =>
      obtain ⟨n, hleaf⟩ := LCS.Propositional.Infinite.Proofs.infSearchPath_crosses_stage_leaf seq address label hp hl k
      have hhead : InfSeq.head (infSearchSteps seq k).L = some A := by
        change (infSearchSteps seq k).L 0 = some A
        rw [(LCS.Propositional.Infinite.Proofs.infSearchSteps_remaining seq k 0).1]
        simpa using hindex
      have huf := unfinished_of_head (infSearchSteps seq k) (label n)
        (LCS.Propositional.Infinite.Proofs.infSearchPath_nonaxiom seq address label hp hl n)
        (Or.inl (by rw [hhead]; simp))
      obtain ⟨m, _, _, _, _, _, _, _, heq, _⟩ :=
        next_stage_expansion_path seq address label hp hl k n hleaf huf
      refine ⟨m, ?_⟩
      rw [heq]
      simp [occurs, extendSeq, hhead]
  | falseF A =>
    obtain ⟨index, hindex⟩ := hs
    cases index with
    | zero =>
      refine ⟨0, ?_⟩
      rw [hroot]
      simp [occurs, infSearchInit, InfSeq.head, hindex]
    | succ k =>
      obtain ⟨n, hleaf⟩ := LCS.Propositional.Infinite.Proofs.infSearchPath_crosses_stage_leaf seq address label hp hl k
      have hhead : InfSeq.head (infSearchSteps seq k).R = some A := by
        change (infSearchSteps seq k).R 0 = some A
        rw [(LCS.Propositional.Infinite.Proofs.infSearchSteps_remaining seq k 0).2]
        simpa using hindex
      have huf := unfinished_of_head (infSearchSteps seq k) (label n)
        (LCS.Propositional.Infinite.Proofs.infSearchPath_nonaxiom seq address label hp hl n)
        (Or.inr (by rw [hhead]; simp))
      obtain ⟨m, _, _, _, _, _, _, _, heq, _⟩ :=
        next_stage_expansion_path seq address label hp hl k n hleaf huf
      refine ⟨m, ?_⟩
      rw [heq]
      simp [occurs, extendSeq, hhead]

helper /-- The union of all signed formulae in the branch, including its root. -/
def branchSignedSet (b : FairOpenBranch) : Set SignedFormula :=
  fun sf => ∃ n, occurs (b.label n) sf

helper theorem branch_atomic_persistence (b : FairOpenBranch) (i j : Nat) (hij : i ≤ j)
    (sf : SignedFormula) (ha : sf.classify = none)
    (h : occurs (b.label i) sf) : occurs (b.label j) sf := by
  have hfalse (S : Set SignedFormula) : ¬expanded S sf := by
    cases sf with
    | trueF A => cases A <;> simp_all [SignedFormula.classify, expanded]
    | falseF A => cases A <;> simp_all [SignedFormula.classify, expanded]
  induction hij with
  | refl => exact h
  | @step j hij ih =>
    exact (branchStep_support (b.step j) sf ih).resolve_right (hfalse _)

helper /-- Proof of Lemma 3.5.2, branch argument: fairness selects a genuine rule;
    that rule provides the components, while persistence excludes opposite atoms.
    This covers infinite branches as well as finite branches with atomic endpoints. -/
theorem fair_branch_hintikka_set_extraction (b : FairOpenBranch) :
    IsHintikkaSet (branchSignedSet b) := by
  have expand (sf : SignedFormula) (h : branchSignedSet b sf)
      (hc : sf.classify ≠ none) : expanded (branchSignedSet b) sf := by
    obtain ⟨n, hn⟩ := h
    obtain ⟨m, _, selected, hm⟩ := b.fair n sf hn hc
    exact expanded_mono (fun sf hf => ⟨m + 1, hf⟩) sf
      (branchPrincipal_expanded selected sf hm)
  constructor
  · intro n ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    have hi := branch_atomic_persistence b i (max i j) (Nat.le_max_left ..) _ rfl hi
    have hj := branch_atomic_persistence b j (max i j) (Nat.le_max_right ..) _ rfl hj
    exact b.isOpen (max i j) ⟨.var n, hi, hj⟩
  · intro a ha
    have hc : a.toSigned.classify ≠ none := by
      cases a <;> simp [TypeA.toSigned, SignedFormula.classify]
    change branchSignedSet b a.comp1 ∧ branchSignedSet b a.comp2
    have h := expand a.toSigned ha hc
    cases a <;> simpa [TypeA.toSigned, TypeA.comp1, TypeA.comp2, expanded] using h
  · intro beta hb
    have hc : beta.toSigned.classify ≠ none := by
      cases beta <;> simp [TypeB.toSigned, SignedFormula.classify]
    change branchSignedSet b beta.comp1 ∨ branchSignedSet b beta.comp2
    have h := expand beta.toSigned hb hc
    cases beta <;> simpa [TypeB.toSigned, TypeB.comp1, TypeB.comp2, expanded] using h

helper /-- The valuation is extracted from the complete branch union. -/
theorem fair_branch_satisfiable (b : FairOpenBranch) :
    SignedSet.satisfiedBy (branchSignedSet b)
      (hintikkaCanonicalValuation (branchSignedSet b)) := by
  intro sf hsf
  have h := canonical_satisfies_combined (branchSignedSet b)
    (fair_branch_hintikka_set_extraction b)
  cases sf with
  | trueF A => exact (h A).1 hsf
  | falseF A => exact (h A).2 hsf

helper /-- All formulas of the starting sequent occur in the corrected path union. -/
theorem root_signedSet_sub_pathSignedSet {s : Sequent} (dt : DeductionTree s)
    (p : Path) (sf : SignedFormula) (h : occurs s sf) :
    pathSignedSet dt p sf :=
  (pathSignedSet_iff dt p sf).mpr ⟨s, root_mem_sequentsAlongPath dt p, h⟩

helper /-- Once every enumerated input formula has entered the branch, its canonical
    valuation falsifies the entire possibly infinite input sequent. -/
theorem fair_branch_falsifies_input (seq : InfSequent) (b : FairOpenBranch)
    (hcover : ∀ sf, signedSetOfSequent seq sf → branchSignedSet b sf) :
    infSeqFalsifies (hintikkaCanonicalValuation (branchSignedSet b)) seq := by
  constructor
  · intro n A hn
    exact fair_branch_satisfiable b (.trueF A) (hcover _ ⟨n, hn⟩)
  · intro n A hn
    exact fair_branch_satisfiable b (.falseF A) (hcover _ ⟨n, hn⟩)

proof_of infinite_search_path_canonical_countermodel := by
  obtain ⟨label, hl, hsteps⟩ := infinite_limit_path_labels seq address hp
  let steps := fun n => Classical.choice (hsteps n)
  let branch : FairOpenBranch :=
    { label := label
      step := steps
      isOpen := LCS.Propositional.Infinite.Proofs.infSearchPath_nonaxiom seq address label hp hl
      fair := infinite_limit_path_fair seq address label hp hl steps }
  exact ⟨label, hl, fair_branch_hintikka_set_extraction branch,
    fair_branch_falsifies_input seq branch (infinite_limit_path_covers_input seq address label hp hl)⟩


proof_of hintikka_set_extraction := by
  by_cases hhalt : infSearchHalts seq
  · obtain ⟨k, hfinished⟩ := hhalt
    have hopen : ¬ ∀ leaf ∈ (infSearchSteps seq k).tree.leaves, isAxiom leaf :=
      fun h => hnotclosed ⟨k, h⟩
    obtain ⟨terminal, labels, hp, hS⟩ :=
      finished_search_hintikka_set_extraction seq k hfinished hopen
    exact Or.inl ⟨k, terminal, labels, hfinished, hp, hS⟩
  · obtain ⟨address, hp⟩ := infSearch_infinitePath_of_not_halts seq hhalt
    obtain ⟨label, hl, hS, _⟩ := infinite_search_path_canonical_countermodel seq address hp
    exact Or.inr ⟨address, label, hp, hl, hS⟩


end LCS.Propositional.Infinite.SignedFormulae
