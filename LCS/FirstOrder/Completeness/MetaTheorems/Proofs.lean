import LCS.FirstOrder.Completeness.MetaTheorems

namespace LCS.FirstOrder.Completeness.MetaTheorems

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SemanticsN (formulaEvalN formulaNoEq
  satisfiableSetN satisfiableSetInN finiteSubsetSatisfiableN isCountableDomain)

open LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Gentzen.Hintikka

open LCS.FirstOrder.Completeness

open LCS.FirstOrder.Completeness.InfiniteSearch (
  signedLimitSet limitSet_isHintikka gamma_in_limitSet)

open LCS.FirstOrder.Gentzen.SignedFormulae
  (SignedFormula)

open LCS.FirstOrder.Gentzen.Hintikka
  (hintikkaStructure identityAssignment IsHintikkaSet
   hintikka_set_satisfiable hintikka_set_satisfiable_concrete)

open LCS.FirstOrder.SyntaxN.Substitution (isFreeForN)

open Classical



helper noncomputable def lindenbaumChain {L : Language} [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) : Nat → Set (FormulaN L)
  | 0 => Gamma
  | n + 1 =>
    let prev := lindenbaumChain Gamma n
    let A := Countable.enumerate n
    if _ : InfiniteSearch.isConsistentSet (fun x => prev x ∨ x = A)
    then fun x => prev x ∨ x = A
    else prev

helper noncomputable def lindenbaumLimit {L : Language} [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) : Set (FormulaN L) :=
  fun A => ∃ n, lindenbaumChain Gamma n A

helper theorem chain_consistent {L : Language}
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) (hCon : InfiniteSearch.isConsistentSet Gamma) :
    ∀ n, InfiniteSearch.isConsistentSet (lindenbaumChain Gamma n) := by
-- BEGIN PROOF
  intro n; induction n with
  | zero => exact hCon
  | succ k ih =>
    show InfiniteSearch.isConsistentSet (
      if _ : InfiniteSearch.isConsistentSet (fun x => lindenbaumChain Gamma k x ∨
        x = Countable.enumerate k)
      then fun x => lindenbaumChain Gamma k x ∨ x = Countable.enumerate k
      else lindenbaumChain Gamma k)
    split <;> assumption

helper theorem chain_mono {L : Language}
    [Countable (FormulaN L)] (Gamma : Set (FormulaN L)) :
    ∀ n A, lindenbaumChain Gamma n A →
      lindenbaumChain Gamma (n + 1) A := by
-- BEGIN PROOF
  intro n A hA
  show (if _ : InfiniteSearch.isConsistentSet (fun x => lindenbaumChain Gamma n x ∨
      x = Countable.enumerate n)
    then fun x => lindenbaumChain Gamma n x ∨ x = Countable.enumerate n
    else lindenbaumChain Gamma n) A
  split
  · exact Or.inl hA
  · exact hA

helper theorem chain_mono_ge {L : Language}
    [Countable (FormulaN L)] (Gamma : Set (FormulaN L)) :
    ∀ n m, n ≤ m → ∀ A, lindenbaumChain Gamma n A →
      lindenbaumChain Gamma m A := by
-- BEGIN PROOF
  intro n m h; induction h with
  | refl => exact fun A hA => hA
  | step _ ih => exact fun A hA => chain_mono Gamma _ A (ih A hA)

helper theorem list_in_limit_bounded {L : Language}
    [Countable (FormulaN L)] (Gamma : Set (FormulaN L))
    (cs : List (FormulaN L))
    (hcs : ∀ c, c ∈ cs → lindenbaumLimit Gamma c) :
    ∃ k, ∀ c, c ∈ cs → lindenbaumChain Gamma k c := by
-- BEGIN PROOF
  induction cs with
  | nil => exact ⟨0, fun _ h => by simp at h⟩
  | cons a as ih =>
    have ha := hcs a List.mem_cons_self
    have has := ih (fun c hc => hcs c (List.mem_cons_of_mem _ hc))
    obtain ⟨ka, hka⟩ := ha
    obtain ⟨kas, hkas⟩ := has
    refine ⟨max ka kas, fun c hc => ?_⟩
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact chain_mono_ge Gamma ka _ (Nat.le_max_left ka kas) _ hka
    · exact chain_mono_ge Gamma kas _ (Nat.le_max_right ka kas) c (hkas c hc)

helper theorem limit_consistent {L : Language}
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) (hCon : InfiniteSearch.isConsistentSet Gamma) :
    InfiniteSearch.isConsistentSet (lindenbaumLimit Gamma) := by
-- BEGIN PROOF
  letI : Nonempty (FormulaN L) := ⟨Countable.enumerate 0⟩
  apply (InfiniteSearch.isConsistentSet_iff_emptySucc (lindenbaumLimit Gamma)).mpr
  intro cs hcs hprov
  obtain ⟨k, hk⟩ := list_in_limit_bounded Gamma cs hcs
  exact (InfiniteSearch.isConsistentSet_iff_emptySucc (lindenbaumChain Gamma k)).mp
    (chain_consistent Gamma hCon k) cs (fun c hc => hk c hc) hprov

helper theorem limit_maximal {L : Language}
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L)) (_hCon : InfiniteSearch.isConsistentSet Gamma) :
    ∀ (Sigma : Set (FormulaN L)),
      InfiniteSearch.isConsistentSet Sigma →
      Set.subset (lindenbaumLimit Gamma) Sigma →
      lindenbaumLimit Gamma = Sigma := by
-- BEGIN PROOF
  intro Sigma hSigmaCon hSub
  funext B; apply propext
  constructor
  · exact fun hB => hSub B hB
  · intro hBSigma
    obtain ⟨n, rfl⟩ := Countable.enumerate_surj B
    have hConExt : InfiniteSearch.isConsistentSet
        (fun x => lindenbaumChain Gamma n x ∨
          x = Countable.enumerate n) := by
      obtain ⟨A, hA⟩ := hSigmaCon
      refine ⟨A, ?_⟩
      intro cs hcs hprov
      exact hA cs (fun c hc =>
          match hcs c hc with
          | Or.inl h => hSub c ⟨n, chain_mono_ge Gamma n n
                          (Nat.le_refl n) c h⟩
          | Or.inr h => by rw [h]; exact hBSigma) hprov
    have hStep : lindenbaumChain Gamma (n + 1) (Countable.enumerate n) := by
      show (if _ : InfiniteSearch.isConsistentSet (fun x => lindenbaumChain Gamma n x ∨
          x = Countable.enumerate n)
        then fun x => lindenbaumChain Gamma n x ∨ x = Countable.enumerate n
        else lindenbaumChain Gamma n) (Countable.enumerate n)
      rw [dif_pos hConExt]; right; rfl
    exact ⟨n + 1, hStep⟩

helper /-- A consistent set is maximally consistent exactly when every proper
superset is inconsistent. -/
theorem isMaximalConsistentSet_iff_proper_superset {L : Language}
    (Gamma : Set (FormulaN L)) (hCon : InfiniteSearch.isConsistentSet Gamma) :
    isMaximalConsistentSet Gamma ↔
      ∀ Delta, Set.subset Gamma Delta → Gamma ≠ Delta →
        ¬ InfiniteSearch.isConsistentSet Delta := by
  constructor
  · intro hMax Delta hSub hNe hDeltaCon
    exact hNe (hMax.2 Delta hDeltaCon hSub)
  · intro hProper
    refine ⟨hCon, fun Delta hDeltaCon hSub => ?_⟩
    exact Classical.byContradiction fun hNe => hProper Delta hSub hNe hDeltaCon

helper /-- Every consistent set Gamma of an enumerated formula language is a
subset of a maximal consistent set Delta. -/
theorem maximal_consistent_extension {L : Language}
    [Countable (FormulaN L)]
    (Gamma : Set (FormulaN L))
    (hCon : InfiniteSearch.isConsistentSet Gamma) :
    ∃ (Delta : Set (FormulaN L)),
      isMaximalConsistentSet Delta ∧ Set.subset Gamma Delta :=
-- BEGIN PROOF
by
  exact ⟨lindenbaumLimit Gamma,
   ⟨⟨limit_consistent Gamma hCon, limit_maximal Gamma hCon⟩,
    fun _ hA => ⟨0, hA⟩⟩⟩

helper /-- Every formula of a language without equality contains no equality atom. -/
theorem formulaNoEq_of_withoutEquality {L : Language} (hL : L.withoutEquality)
    (A : FormulaN L) : formulaNoEq A := by
  induction A with
  | predN => trivial
  | eq_ h _ _ => simp [Language.withoutEquality] at hL; simp [hL] at h
  | neg _ ih => exact ih
  | conj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | disj _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | impl _ _ ihA ihB => exact ⟨ihA, ihB⟩
  | all _ _ ih => exact ih
  | ex _ _ ih => exact ih

proof_of isMaximalConsistentSet_iff_proper_supersetNoEq := isMaximalConsistentSet_iff_proper_superset Gamma hCon


proof_of satisfiable_implies_consistentNNoEq := satisfiable_implies_consistentN Gamma hSat


proof_of consistent_implies_satisfiableNNoEq := by
  rcases Classical.em (Nonempty (FormulaN L)) with hNE | hEmpty
  · letI := hNE
    letI := Countable.ofAtMostCountable (α := FormulaN L)
    exact consistent_implies_satisfiableN Gamma hCon hFB
      (fun A _ => formulaNoEq_of_withoutEquality hL A)
  · obtain ⟨A, _⟩ := hCon
    exact False.elim (hEmpty ⟨A⟩)


proof_of lowenheim_skolemNoEq := by
  rcases Classical.em (Nonempty (FormulaN L)) with hNE | hEmpty
  · letI := hNE
    letI := Countable.ofAtMostCountable (α := FormulaN L)
    exact lowenheim_skolem Gamma hSat (fun A _ => formulaNoEq_of_withoutEquality hL A)
  · let M : Structure L := {
      carrier := Unit
      carrierNonempty := ⟨()⟩
      interpFunc := fun _ _ => ()
      interpConst := fun _ => ()
      interpPred := fun _ _ => True }
    refine ⟨M, ⟨fun _ => (), fun A _ => False.elim (hEmpty ⟨A⟩)⟩, ?_⟩
    exact ⟨fun _ => (), fun u => ⟨0, by cases u; rfl⟩⟩


proof_of compactnessNoEq := by
  rcases Classical.em (Nonempty (FormulaN L)) with hNE | hEmpty
  · letI := hNE
    letI := Countable.ofAtMostCountable (α := FormulaN L)
    exact compactness Gamma hFSS (fun A _ => formulaNoEq_of_withoutEquality hL A)
  · let M : Structure L := {
      carrier := Unit
      carrierNonempty := ⟨()⟩
      interpFunc := fun _ _ => ()
      interpConst := fun _ => ()
      interpPred := fun _ _ => True }
    exact ⟨M, fun _ => (), fun A _ => False.elim (hEmpty ⟨A⟩)⟩


proof_of maximal_consistent_extensionNoEq := by
  rcases Classical.em (Nonempty (FormulaN L)) with hNE | hEmpty
  · letI := hNE
    letI := Countable.ofAtMostCountable (α := FormulaN L)
    exact maximal_consistent_extension Gamma hCon
  · obtain ⟨A, _⟩ := hCon
    exact False.elim (hEmpty ⟨A⟩)


helper /-- Without equality or predicate symbols there are no normalized formulae. -/
theorem formulaN_not_nonemptyNoEq {L : Language} (hL : L.withoutEquality)
    (hPred : L.predSymbols → False) : ¬ Nonempty (FormulaN L) := by
  rintro ⟨A⟩
  induction A with
  | predN P _ => exact hPred P
  | eq_ h _ _ => simp [Language.withoutEquality] at hL; simp [hL] at h
  | neg _ ih => exact ih
  | conj _ _ ih _ => exact ih
  | disj _ _ ih _ => exact ih
  | impl _ _ ih _ => exact ih
  | all _ _ ih => exact ih
  | ex _ _ ih => exact ih

helper /-- In the empty-formula language the empty set is satisfiable but fails
existential consistency. -/
theorem emptySet_satisfiable_not_consistentNoEq {L : Language}
    (hL : L.withoutEquality) (hPred : L.predSymbols → False) :
    satisfiableSetN (∅ : Set (FormulaN L)) ∧
      ¬ InfiniteSearch.isConsistentSetNoEq hL (∅ : Set (FormulaN L)) := by
  constructor
  · let M : Structure L := {
      carrier := Unit
      carrierNonempty := ⟨()⟩
      interpFunc := fun _ _ => ()
      interpConst := fun _ => ()
      interpPred := fun _ _ => True }
    exact ⟨M, fun _ => (), fun _ h => False.elim h⟩
  · rintro ⟨A, _⟩
    exact formulaN_not_nonemptyNoEq hL hPred ⟨A⟩

proof_of nonclosed_search_path_hintikka_model := by
  have hSat := hintikka_set_satisfiable_concrete hL path.termDomain S hHS
  refine ⟨hSat, ?_⟩
  intro A hA
  have hInput := (hGamma A).mpr hA
  have hIn : SignedFormula.trueF A ∈ S := by
    -- REPAIR(T110): proof pending
    sorry
  exact hSat (SignedFormula.trueF A) hIn


end LCS.FirstOrder.Completeness.MetaTheorems
