import LCS.FirstOrder.Equality.Search.Part2

section

namespace LCS.FirstOrder.Equality.Search

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.Gentzen LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Completeness.Search

helper /-- Definition 5.6.3: The finished test is precisely the axiom test,
independent of remaining input, terms or formula records. -/
theorem isFinishedLeaf_iff_axiom {L : Language} (hL : L.hasEquality = true)
    {root : Sequent L} (st : SearchState L root) (s : Sequent L)
    (records : BranchRecords L) : isFinishedLeaf hL st s records ↔ isAxiom s := Iff.rfl

helper /-- Definition 5.6.3: Expanding a designated leaf preserves all existing
edges, including input-introduction edges. -/
theorem expand_extends {L : Language} (hL : L.hasEquality = true) {root : Sequent L}
    (path : List Nat) (st : SearchState L root) :
    InfGDeductionTreeExt.Extension st.tree.forget (expand hL path st).tree.forget := by
  induction path generalizing root with
  | nil =>
    cases ht : st.tree with
    | leaf s records =>
      simp only [expand, ht, SearchTree.forget]
      exact .leaf _
    | onePremise => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
    | twoPremise => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
    | extend => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
    | extendEq => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
  | cons i path ih =>
    cases i with
    | zero =>
      cases ht : st.tree with
      | leaf => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
      | onePremise rule sub =>
        simpa only [Nat.zero_add, expand, ht, SearchState.withTree, SearchTree.forget] using
          InfGDeductionTreeExt.Extension.one rule (ih (st.withTree sub))
      | twoPremise rule left right =>
        simpa only [Nat.zero_add, expand, ht, SearchState.withTree, SearchTree.forget] using
          InfGDeductionTreeExt.Extension.two rule (ih (st.withTree left))
            (InfGDeductionTreeExt.Extension.refl right.forget)
      | extend a b sub =>
        simpa only [Nat.zero_add, expand, ht, SearchState.withTree, SearchTree.forget] using
          InfGDeductionTreeExt.Extension.intro a b (ih (st.withTree sub))
      | extendEq a b hs hn sub =>
        simpa only [Nat.zero_add, expand, ht, SearchState.withTree, SearchTree.forget] using
          InfGDeductionTreeExt.Extension.eqIntro a b hs hn (ih (st.withTree sub))
    | succ i =>
      cases i with
      | zero =>
        cases ht : st.tree with
        | twoPremise rule left right =>
          simpa only [Nat.zero_add, expand, ht, SearchState.withTree, SearchTree.forget] using
            InfGDeductionTreeExt.Extension.two rule (InfGDeductionTreeExt.Extension.refl left.forget)
              (ih (st.withTree right))
        | leaf => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
        | onePremise => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
        | extend => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
        | extendEq => simpa only [Nat.zero_add, expand, ht] using InfGDeductionTreeExt.Extension.refl st.tree.forget
      | succ i => simpa only [expand] using InfGDeductionTreeExt.Extension.refl st.tree.forget

helper /-- Definition 5.6.3: A sequence of designated-leaf expansions extends the
initial tree, with each expansion using the updated global state. -/
theorem expandFold_extends {L : Language} (hL : L.hasEquality = true) {root : Sequent L}
    (paths : List (List Nat)) (st : SearchState L root) :
    InfGDeductionTreeExt.Extension st.tree.forget
      (paths.foldl (fun acc path => expand hL path acc) st).tree.forget := by
  induction paths generalizing st with
  | nil => exact .refl _
  | cons path paths ih => exact (expand_extends hL path st).trans (ih (expand hL path st))

helper /-- Definition 5.6.3: Each round preserves every previous tree node and edge. -/
theorem searchRound_extends {L : Language} (hL : L.hasEquality = true) {root : Sequent L}
    (st : SearchState L root) :
    InfGDeductionTreeExt.Extension st.tree.forget (searchRound hL st).tree.forget := by
  classical
  by_cases h : allFinished hL st
  · simp only [searchRound, ite_eq_left h]
    exact .refl _
  · simpa only [searchRound, ite_eq_right h, roundEndUpdate, advanceInput,
      SearchTree.forget_commitRound, startRound, SearchTree.forget_startRound] using
      expandFold_extends hL st.tree.leafAddresses (startRound st)

helper /-- Definition 5.6.3: The finite round approximants are monotone: round k+1
extends round k, retaining all G-rule, input-introduction, and equality-packet edges. -/
theorem searchEq_monotone {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) (k : Nat) :
    InfGDeductionTreeExt.Extension (searchEq hL q hq hFB enum eqEnum k).tree.forget
      (searchEq hL q hq hFB enum eqEnum (k + 1)).tree.forget :=
  searchRound_extends hL _

helper /-- Definition 5.6.3: A node remains at the same address in every later round. -/
theorem searchEq_labelAt_mono {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) (k n : Nat) (p : List Nat) (label : Sequent L)
    (hp : (searchEq hL q hq hFB enum eqEnum k).tree.forget.labelAt p = some label) :
    (searchEq hL q hq hFB enum eqEnum (k + n)).tree.forget.labelAt p = some label := by
  induction n with
  | zero => exact hp
  | succ n ih => exact (searchEq_monotone hL q hq hFB enum eqEnum (k + n)).labelAt_preserves p label ih

helper /-- Definition 5.6.3: The union of finite search stages assigns a unique
label to each address. -/
theorem searchLimitEq_unique {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q) (p : List Nat) (s t : Sequent L)
    (hs : searchLimitEq hL q hq hFB enum eqEnum p s)
    (ht : searchLimitEq hL q hq hFB enum eqEnum p t) : s = t := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj⟩ := ht
  have hi' := searchEq_labelAt_mono hL q hq hFB enum eqEnum i j p s hi
  have hj' := searchEq_labelAt_mono hL q hq hFB enum eqEnum j i p t hj
  rw [Nat.add_comm j i] at hj'
  rw [hi'] at hj'
  exact Option.some.inj hj'

proof_of infinitePath_yields_hintikkaSetEq := by
  -- REPAIR(T117): proof pending
  sorry


proof_of searchCompletenessEqValid := by
  -- REPAIR(T118): proof pending
  sorry


helper /-- Theorem 5.6.1(ii): The explicit equality quotient of a countable
Hintikka term domain falsifies every input whose signed formulae belong to S.
Its canonical assignment satisfies all antecedents and falsifies all succedents;
the quotient carrier is finite or countably infinite. -/
theorem falsifiableInQuotient {L : Language} (hL : L.hasEquality = true)
    (q : InfSequentN L) (H : Set (Term L)) (S : Set (SignedFormula L))
    (hHS : IsHintikkaSetEq L hL H S)
    (hH : AtMostCountable {t : Term L // t ∈ H})
    (hAnt : ∀ A, q.memAntecedent A → SignedFormula.trueF A ∈ S)
    (hSucc : ∀ B, q.memSuccedent B → SignedFormula.falseF B ∈ S) :
    let M := quotientStructureEq hL H S hHS
    let s := quotAssignment hL H S hHS
    LCS.FirstOrder.SemanticsN.isCountableDomain M ∧
      (∀ A, q.memAntecedent A → LCS.FirstOrder.SemanticsN.formulaEvalN M A s) ∧
      (∀ B, q.memSuccedent B → ¬ LCS.FirstOrder.SemanticsN.formulaEvalN M B s) := by
  classical
  letI : AtMostCountable {t : Term L // t ∈ H} := hH
  letI : Nonempty {t : Term L // t ∈ H} :=
    ⟨⟨hHS.base.hTA.nonempty.choose, hHS.base.hTA.nonempty.choose_spec⟩⟩
  letI : Countable {t : Term L // t ∈ H} := Countable.ofAtMostCountable
  refine ⟨?_, ?_, ?_⟩
  · change ∃ f : Nat → QType hL H S hHS, Function.Surjective f
    refine ⟨fun n => qmk (Countable.enumerate n), ?_⟩
    intro b
    refine Quotient.inductionOn b ?_
    intro t
    obtain ⟨n, hn⟩ := Countable.enumerate_surj t
    exact ⟨n, congrArg (fun a => @qmk L hL H S hHS a) hn⟩
  · intro A hA
    exact hintikka_set_eq_satisfiable hL H S hHS (.trueF A) (hAnt A hA)
  · intro B hB
    exact hintikka_set_eq_satisfiable hL H S hHS (.falseF B) (hSucc B hB)

proof_of searchCompletenessEqFalsifiable := by
  -- REPAIR(T119): proof pending
  sorry


proof_of goedelExtendedCompletenessGEq := by
  constructor
  · intro hValid
    -- REPAIR(T120): proof pending
    sorry
  · rintro ⟨seq, hSub, hProof⟩ M s hAnt
    have hMem (xs : List (FormulaN L.toLanguage))
        (a : Nat → Option (FormulaN L.toLanguage))
        (h : LCS.FirstOrder.Completeness.IsFiniteSubsequenceN xs a)
        (A : FormulaN L.toLanguage) (hA : A ∈ xs) : ∃ n, a n = some A := by
      obtain ⟨pos, _, hpos⟩ := h
      obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hA
      exact ⟨pos ⟨i, hi⟩, (hpos ⟨i, hi⟩).trans (congrArg some hget)⟩
    obtain ⟨B, hB, hTrue⟩ := soundnessGEq hL seq hProof M s
      (fun A hA => hAnt A (hMem _ _ hSub.1 A hA))
    exact ⟨B, hMem _ _ hSub.2 B hB, hTrue⟩


helper /-- Definition 5.6.3, hence-clause: For every admissible equality-search
run on a nonvalid input containing equality, the actual limit tree has an
infinite path. -/
theorem notValid_searchEq_hasInfinitePath {L : FirstOrderLanguage}
    (hL : L.hasEquality = true)
    (q : InfSequentN L.toLanguage) (hq : q.builtFromX) (hFB : crossNoFreeBoundInf q)
    (enum : SearchEnumeration q) (eqEnum : EqEnumeration hL q)
    (hEq : ∃ A, (q.memAntecedent A ∨ q.memSuccedent A) ∧
      ¬ LCS.FirstOrder.SemanticsN.formulaNoEq A)
    (hNotValid : ¬ infSequentValid q) :
    let run : Run L hL := ⟨q, hq, hFB, enum, eqEnum⟩
    ∃ path, run.IsInfinitePath path := by
  have hFals : infSequentFalsifiable q :=
    Classical.byContradiction fun hNotFals =>
      hNotValid (fun M s hAnt => Classical.byContradiction fun hNoSucc =>
        hNotFals ⟨M, s, hAnt, fun B hB hEval => hNoSucc ⟨B, hB, hEval⟩⟩)
  obtain ⟨_, path, hPath, _⟩ :=
    searchCompletenessEqFalsifiable hL q hq hFB enum eqEnum hEq hFals
  exact ⟨path, hPath⟩

proof_of quantifierFree_searchEq_mayDiverge := by
  -- REPAIR(T121): proof pending
  sorry


helper /-- Theorem 5.6.1, comparison with §5.5: Every admissible search51 run
on a finite quantifier-free input in a language without equality halts. -/
theorem quantifierFree_search51_halts {L : Language} (hL : L.withoutEquality)
    (seq : Sequent L) (hq : (InfSequentN.ofSequent seq).builtFromX)
    (hFB : crossNoFreeBoundInf (InfSequentN.ofSequent seq))
    (enum : SearchEnumeration (InfSequentN.ofSequent seq))
    (hQF : LCS.FirstOrder.Completeness.sequentQuantifierFree seq) :
    LCS.FirstOrder.Completeness.Search.halts51 hL (InfSequentN.ofSequent seq)
      hq hFB enum :=
  (LCS.FirstOrder.Completeness.quantifierFreeDecidableF hL seq hq hFB enum hQF).1

helper /-- Theorem 5.6.1, equality-rule remark: A reflexivity-rule deduction
introduces a premise formula absent from both sides of its conclusion. -/
theorem equalityRule_adds_new_formula {L : Language} (hL : L.hasEquality = true) :
    ∃ t : Term L,
      let A := FormulaN.eq_ hL t t
      let premise : Sequent L := .mk [A] []
      let tree := GEqDeductionTree.eqRefl t [] [] (.leaf premise)
      A ∈ premise.antecedent ∧ A ∉ tree.conclusion.antecedent ∧
        A ∉ tree.conclusion.succedent := by
  refine ⟨Term.var 0, ?_⟩
  simp [GEqDeductionTree.conclusion]

helper /-- Definition 5.6.3, level-0 remark: Every term in the level-0 domain
occurs in the admissible TERMS enumeration of the input. -/
theorem levelZero_terms_in_TERMS {L : Language} (q : InfSequentN L)
    (terms : TermsEnum q) (t : Term L) (ht : levelTerm q 0 t) :
    ∃ n, terms.entries n = some t := by
  apply (terms.enumerates t).mpr
  rcases ht with ht | ⟨k, hk, hk0, _⟩
  · exact ht
  · omega

helper /-- Definition 5.6.3: All node sequents of a G_= deduction tree,
including the premises of every ordinary and generalized equality rule. -/
def eqDeductionSequents {L : Language} {hL : L.hasEquality = true} :
    {s : Sequent L} → GEqDeductionTree hL s → List (Sequent L)
  | _, .leaf s => [s]
  | s, .onePremise _ sub => s :: eqDeductionSequents sub
  | s, .twoPremise _ left right => s :: (eqDeductionSequents left ++ eqDeductionSequents right)
  | _, .eqRefl _ Γ Δ sub => Sequent.mk Γ Δ :: eqDeductionSequents sub
  | _, .eqFuncCong _ _ _ Γ Δ sub => Sequent.mk Γ Δ :: eqDeductionSequents sub
  | _, .eqPredCong _ _ _ Γ Δ sub => Sequent.mk Γ Δ :: eqDeductionSequents sub
  | _, .eqGeneral _ _ _ Γ Δ sub => Sequent.mk Γ Δ :: eqDeductionSequents sub

helper /-- Definition 5.6.3, failure for G_=: A single generalized equality rule
adds reflexivity to the antecedent above the empty root. -/
def eqGeneralCounterTree {L : Language} (hL : L.hasEquality = true) :
    GEqDeductionTree hL (Sequent.mk [] []) :=
  .eqGeneral [.eq_ hL (.var 0) (.var 0)] (by simp)
    (by intro A hA; simp only [List.mem_singleton] at hA; subst A
        exact Or.inl ⟨.var 0, rfl⟩)
    [] [] (.leaf (Sequent.mk [.eq_ hL (.var 0) (.var 0)] []))

helper /-- Definition 5.6.3, failure for G_=: The concrete generalized-equality
counterexample has a premise occurrence that is neither a subformula nor a
signed descendant of any root formula. -/
theorem eqGeneral_subformulaProperty_fails {L : Language} (hL : L.hasEquality = true) :
    ∃ node ∈ eqDeductionSequents (eqGeneralCounterTree hL),
      ∃ A ∈ sequentSignedFormulae node,
        ¬ RootSubformula (Sequent.mk [] []) (signedFormulaBody A) ∧
        ¬ RootDescendant (Sequent.mk [] []) A := by
  refine ⟨Sequent.mk [.eq_ hL (.var 0) (.var 0)] [], ?_,
    .trueF (.eq_ hL (.var 0) (.var 0)), ?_, ?_, ?_⟩
  · simp [eqDeductionSequents, eqGeneralCounterTree]
  · simp [sequentSignedFormulae]
  · simp [RootSubformula]
  · simp [RootDescendant, sequentSignedFormulae]

proof_of consistent_emptySucc_falsifiable := by
  -- REPAIR(T123): proof pending
  sorry


proof_of nonclosed_search_path_hintikka_model := by
  have hSat := hintikka_set_eq_satisfiable hL run.termDomain S hHS
  refine ⟨rfl, hSat, ?_⟩
  intro A hA
  apply hSat (.trueF A)
  -- REPAIR(T123): proof pending
  sorry


helper /-- Theorem 5.6.4, finite-model remark: In every first-order language with
equality, a satisfiable theory can force its models to be finite. The theory
∀x₀ ∀x₁ (x₀ ≐ x₁) forces a singleton, so the Löwenheim-Skolem model may be finite. -/
theorem lowenheimSkolem_model_may_be_finite {L : FirstOrderLanguage}
    (hL : L.hasEquality = true) :
    ∃ Gamma : Set (FormulaN L.toLanguage),
      LCS.FirstOrder.SemanticsN.satisfiableSetN Gamma ∧
      ∀ (M : Structure L.toLanguage) (s : Assignment M),
        (∀ A ∈ Gamma, LCS.FirstOrder.SemanticsN.formulaEvalN M A s) →
        LCS.FirstOrder.SemanticsN.isFiniteDomain M := by
  classical
  let A : FormulaN L.toLanguage := .all 0 (.all 1 (.eq_ hL (.var 0) (.var 1)))
  refine ⟨fun F => F = A, ?_, ?_⟩
  · let M : Structure L.toLanguage :=
      { carrier := Unit, carrierNonempty := ⟨()⟩,
        interpFunc := fun _ _ => (), interpConst := fun _ => (),
        interpPred := fun _ _ => True }
    refine ⟨M, fun _ => (), ?_⟩
    intro F hF
    subst F
    change ∀ a b : Unit, a = b
    exact fun a b => Subsingleton.elim a b
  · intro M s hSat
    have hAll : ∀ a b : M.carrier, a = b := by
      have h := hSat A rfl
      simpa [A, LCS.FirstOrder.SemanticsN.formulaEvalN, termEval, assignUpdate] using h
    let a : M.carrier := Classical.choice M.carrierNonempty
    exact ⟨1, fun _ => a, fun b => ⟨⟨0, by decide⟩, hAll a b⟩⟩

end LCS.FirstOrder.Equality.Search

end
