import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand
import LCS.Herbrand.SHGTheorem.Main.GroundMatrixInstances

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

-- ===================================================================
-- Theorem 7.6.1: CInstance-to-ground-conjunction bridge
-- ===================================================================

/- Enumerate the complete substitution paths represented by a
`CInstance`. A non-universal root contributes exactly the singleton
empty path: in particular, a quantifier-free conjunctive matrix remains
one matrix leaf rather than being split into its connective children.
At a universal node, every child path is retained in constructor order
and extended by the current binder and its chosen closed term. -/
-- ATTACH-BLOCKER: mutual
mutual
def cInstanceGroundSubstitutionPaths {L : Language} :
    CInstance L → List (List (Nat × Term L))
  | .forallInst x _ t₀ h₀ tsRest hsRest _ _ =>
    (cInstanceGroundSubstitutionPaths h₀).map
        (fun path => (x, t₀) :: path) ++
      cInstanceGroundSubstitutionPathsList x tsRest hsRest
  | _ => [[]]

def cInstanceGroundSubstitutionPathsList {L : Language}
    (x : Nat) :
    List (Term L) → List (CInstance L) →
      List (List (Nat × Term L))
  | [], _ => []
  | _ :: _, [] => []
  | t :: tsRest, h :: hsRest =>
    (cInstanceGroundSubstitutionPaths h).map
        (fun path => (x, t) :: path) ++
      cInstanceGroundSubstitutionPathsList x tsRest hsRest
end

/- Every term recorded in an enumerated substitution path is one of the
closed choices carried by a `forallInst` constructor. -/
-- ATTACH-BLOCKER: mutual
mutual
theorem cInstanceGroundSubstitutionPaths_termsClosed
    {L : Language} :
    ∀ (ci : CInstance L)
      (path : List (Nat × Term L)),
      path ∈ cInstanceGroundSubstitutionPaths ci →
      ∀ p ∈ path, Term.isClosed p.2
  | .atom _ _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    simp
  | .negAtom _ _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    simp
  | .connective _ _ _ _ _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    simp
  | .forallInst x C t₀ h₀ tsRest hsRest
      hGround₀ hGroundRest, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_append, List.mem_map] at hPath
    rcases hPath with ⟨tail, hTail, rfl⟩ | hRest
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hGround₀
      · exact
          cInstanceGroundSubstitutionPaths_termsClosed
            h₀ tail hTail p hp
    · exact
        cInstanceGroundSubstitutionPathsList_termsClosed
          x tsRest hsRest hGroundRest path hRest

private theorem cInstanceGroundSubstitutionPathsList_termsClosed
    {L : Language} (x : Nat) :
    ∀ (ts : List (Term L)) (hs : List (CInstance L)),
      (∀ t ∈ ts, Term.isClosed t) →
      ∀ path ∈
          cInstanceGroundSubstitutionPathsList x ts hs,
        ∀ p ∈ path, Term.isClosed p.2
  | [], _, _, path, hPath => by
    simp [cInstanceGroundSubstitutionPathsList] at hPath
  | _ :: _, [], _, path, hPath => by
    simp [cInstanceGroundSubstitutionPathsList] at hPath
  | t :: tsRest, h :: hsRest, hGround, path, hPath => by
    simp only [cInstanceGroundSubstitutionPathsList,
      List.mem_append, List.mem_map] at hPath
    rcases hPath with ⟨tail, hTail, rfl⟩ | hRest
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hGround t List.mem_cons_self
      · exact
          cInstanceGroundSubstitutionPaths_termsClosed
            h tail hTail p hp
    · exact
        cInstanceGroundSubstitutionPathsList_termsClosed
          x tsRest hsRest
          (fun t' ht' =>
            hGround t' (List.mem_cons_of_mem _ ht'))
          path hRest
end

/- Well-formedness aligns every enumerated path with the exact ordered
universal prefix of the represented source. -/
-- ATTACH-BLOCKER: mutual
mutual
theorem cInstanceGroundSubstitutionPaths_complete
    {L : Language} :
    ∀ (ci : CInstance L),
      CInstance.WellFormed ci →
      UniversalPrenexFormula ci.source →
      ∀ path ∈ cInstanceGroundSubstitutionPaths ci,
        path.map Prod.fst =
          (prenexPrefix ci.source).map Prod.snd
  | .atom B hAtom, _, _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    simpa [CInstance.source] using
      Herbrand.isQuantifierFree_prenexPrefix_eq_nil
        B (isAtomic_isQuantifierFree B hAtom)
  | .negAtom B hAtom, _, _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    simp [CInstance.source, prenexPrefix]
  | .connective star C D H K, _, _, path, hPath => by
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_singleton] at hPath
    subst path
    cases star <;> simp [CInstance.source, prenexPrefix]
  | .forallInst x C t₀ h₀ tsRest hsRest
      hGround₀ hGroundRest, hWF, hUniversal, path, hPath => by
    simp only [CInstance.WellFormed] at hWF
    obtain ⟨hSource₀, hWF₀, hWFRest⟩ := hWF
    change
      UniversalPrenexFormula (FormulaN.all x C)
        at hUniversal
    have hBodyUniversal :
        UniversalPrenexFormula C :=
      universalPrenexFormula_body_of_all
        C x hUniversal
    simp only [cInstanceGroundSubstitutionPaths,
      List.mem_append, List.mem_map] at hPath
    rcases hPath with ⟨tail, hTail, rfl⟩ | hRest
    · have hChildUniversal :
          UniversalPrenexFormula h₀.source := by
        rw [hSource₀]
        exact
          universalPrenexFormula_formulaSubstN
            C t₀ x hBodyUniversal
      have hTailComplete :=
        cInstanceGroundSubstitutionPaths_complete
          h₀ hWF₀ hChildUniversal tail hTail
      rw [hSource₀, prenexPrefix_formulaSubstN]
        at hTailComplete
      simpa [CInstance.source, prenexPrefix] using
        congrArg (List.cons x) hTailComplete
    · exact
        cInstanceGroundSubstitutionPathsList_complete
          x C hBodyUniversal tsRest hsRest hWFRest
          path hRest

private theorem cInstanceGroundSubstitutionPathsList_complete
    {L : Language} (x : Nat) (C : FormulaN L)
    (hBodyUniversal : UniversalPrenexFormula C) :
    ∀ (ts : List (Term L)) (hs : List (CInstance L)),
      CInstance.WellFormedList x C ts hs →
      ∀ path ∈
          cInstanceGroundSubstitutionPathsList x ts hs,
        path.map Prod.fst =
          (prenexPrefix (FormulaN.all x C)).map Prod.snd
  | [], [], _, path, hPath => by
    simp [cInstanceGroundSubstitutionPathsList] at hPath
  | [], _ :: _, hWF, _, _ => by
    exact hWF.elim
  | _ :: _, [], hWF, _, _ => by
    exact hWF.elim
  | t :: tsRest, h :: hsRest, hWF, path, hPath => by
    simp only [CInstance.WellFormedList] at hWF
    obtain ⟨hSource, hWFHead, hWFTail⟩ := hWF
    simp only [cInstanceGroundSubstitutionPathsList,
      List.mem_append, List.mem_map] at hPath
    rcases hPath with ⟨tail, hTail, rfl⟩ | hRest
    · have hChildUniversal :
          UniversalPrenexFormula h.source := by
        rw [hSource]
        exact
          universalPrenexFormula_formulaSubstN
            C t x hBodyUniversal
      have hTailComplete :=
        cInstanceGroundSubstitutionPaths_complete
          h hWFHead hChildUniversal tail hTail
      rw [hSource, prenexPrefix_formulaSubstN]
        at hTailComplete
      simpa [prenexPrefix] using
        congrArg (List.cons x) hTailComplete
    · exact
        cInstanceGroundSubstitutionPathsList_complete
          x C hBodyUniversal tsRest hsRest hWFTail
          path hRest
end

private theorem cInstance_toFormula_eq_source_of_qf
    {L : Language} (ci : CInstance L)
    (hWF : CInstance.WellFormed ci)
    (hQF : FirstOrder.SemanticsN.isQuantifierFree ci.source) :
    ci.toFormula = ci.source := by
  cases ci with
  | atom _ _ =>
    simp only [CInstance.toFormula, CInstance.source]
  | negAtom _ _ =>
    simp only [CInstance.toFormula, CInstance.source]
  | connective star C D H K =>
    simp only [CInstance.WellFormed] at hWF
    obtain ⟨hSourceH, hSourceK, hWFH, hWFK⟩ := hWF
    cases star with
    | false =>
      simp only [CInstance.source,
        FirstOrder.SemanticsN.isQuantifierFree] at hQF
      have hQFH :
          FirstOrder.SemanticsN.isQuantifierFree H.source := by
        rw [hSourceH]
        exact hQF.1
      have hQFK :
          FirstOrder.SemanticsN.isQuantifierFree K.source := by
        rw [hSourceK]
        exact hQF.2
      simp only [CInstance.toFormula, CInstance.source]
      rw [cInstance_toFormula_eq_source_of_qf H hWFH hQFH,
        cInstance_toFormula_eq_source_of_qf K hWFK hQFK,
        hSourceH, hSourceK]
    | true =>
      simp only [CInstance.source,
        FirstOrder.SemanticsN.isQuantifierFree] at hQF
      have hQFH :
          FirstOrder.SemanticsN.isQuantifierFree H.source := by
        rw [hSourceH]
        exact hQF.1
      have hQFK :
          FirstOrder.SemanticsN.isQuantifierFree K.source := by
        rw [hSourceK]
        exact hQF.2
      simp only [CInstance.toFormula, CInstance.source]
      rw [cInstance_toFormula_eq_source_of_qf H hWFH hQFH,
        cInstance_toFormula_eq_source_of_qf K hWFK hQFK,
        hSourceH, hSourceK]
  | forallInst _ _ _ _ _ _ _ _ =>
    exact hQF.elim
termination_by sizeOf ci /- ATTACH-BLOCKER: private declaration -/

private theorem applyGroundSubstitution_cons_prenexMatrix_all
    {L : Language} (C : FormulaN L) (x : Nat)
    (t : Term L) (tail : List (Nat × Term L))
    (hx : ¬x ∈ formulaBVN C) :
    applyGroundSubstitution
        (prenexMatrix (FormulaN.all x C))
        ((x, t) :: tail) =
      applyGroundSubstitution
        (prenexMatrix (formulaSubstN C t x)) tail := by
  simp only [prenexMatrix, applyGroundSubstitution,
    List.foldl_cons]
  rw [Herbrand.prenexMatrix_formulaSubstN_of_not_bv
    C t x hx] /- ATTACH-BLOCKER: private declaration -/

/- The enumerated leaves flatten exactly to `CInstance.toFormula`.
The right-nested helper follows the `forallInst` output; both list
certificates preserve each child's leaves without deduplication. -/
mutual
private theorem cInstanceGroundSubstitutionPaths_flattening
    {L : Language} :
    ∀ (ci : CInstance L),
      CInstance.WellFormed ci →
      UniversalPrenexFormula ci.source →
      distinctQuantifierBindings ci.source →
      ConjunctionFlattening ci.toFormula
        ((cInstanceGroundSubstitutionPaths ci).map
          (fun path =>
            applyGroundSubstitution
              (prenexMatrix ci.source) path))
  | .atom B hAtom, _, _, _ => by
    have hQF :
        FirstOrder.SemanticsN.isQuantifierFree B :=
      isAtomic_isQuantifierFree B hAtom
    have hMatrix :=
      Herbrand.isQuantifierFree_prenexMatrix_eq_self
        B hQF
    simpa [cInstanceGroundSubstitutionPaths,
      CInstance.toFormula, CInstance.source,
      applyGroundSubstitution, hMatrix] using
      (ConjunctionFlattening.leaf B)
  | .negAtom B hAtom, _, _, _ => by
    have hQF :
        FirstOrder.SemanticsN.isQuantifierFree
          (FormulaN.neg B) :=
      isAtomic_isQuantifierFree B hAtom
    have hMatrix :=
      Herbrand.isQuantifierFree_prenexMatrix_eq_self
        (FormulaN.neg B) hQF
    simpa [cInstanceGroundSubstitutionPaths,
      CInstance.toFormula, CInstance.source,
      applyGroundSubstitution, hMatrix] using
      (ConjunctionFlattening.leaf (FormulaN.neg B))
  | .connective star C D H K, hWF, hUniversal, _ => by
    have hQF :
        FirstOrder.SemanticsN.isQuantifierFree
          (CInstance.source
            (.connective star C D H K)) := by
      cases star <;> exact hUniversal.1
    have hToFormula :=
      cInstance_toFormula_eq_source_of_qf
        (.connective star C D H K) hWF hQF
    have hMatrix :=
      Herbrand.isQuantifierFree_prenexMatrix_eq_self
        (CInstance.source
          (.connective star C D H K)) hQF
    rw [hToFormula]
    simpa [cInstanceGroundSubstitutionPaths,
      applyGroundSubstitution, hMatrix] using
      (ConjunctionFlattening.leaf
        (CInstance.source
          (.connective star C D H K)))
  | .forallInst x C t₀ h₀ tsRest hsRest
      hGround₀ hGroundRest, hWF, hUniversal, hDistinct => by
    simp only [CInstance.WellFormed] at hWF
    obtain ⟨hSource₀, hWF₀, hWFRest⟩ := hWF
    change
      UniversalPrenexFormula (FormulaN.all x C)
        at hUniversal
    change
      distinctQuantifierBindings (FormulaN.all x C)
        at hDistinct
    have hBodyUniversal :
        UniversalPrenexFormula C :=
      universalPrenexFormula_body_of_all
        C x hUniversal
    have hBodyDistinct :
        distinctQuantifierBindings C :=
      hDistinct.1
    have hxNotBound : ¬x ∈ formulaBVN C :=
      hDistinct.2
    have hChildUniversal :
        UniversalPrenexFormula h₀.source := by
      rw [hSource₀]
      exact
        universalPrenexFormula_formulaSubstN
          C t₀ x hBodyUniversal
    have hChildDistinct :
        distinctQuantifierBindings h₀.source := by
      rw [hSource₀]
      exact
        Herbrand.distinctQuantifierBindings_of_formulaSubstN
          C t₀ x hBodyDistinct
    have hFlattening₀ :=
      cInstanceGroundSubstitutionPaths_flattening
        h₀ hWF₀ hChildUniversal hChildDistinct
    have hLeaves₀ :
        (cInstanceGroundSubstitutionPaths h₀).map
            (fun tail =>
              applyGroundSubstitution
                (prenexMatrix h₀.source) tail) =
          (cInstanceGroundSubstitutionPaths h₀).map
            (fun tail =>
              applyGroundSubstitution
                (prenexMatrix (FormulaN.all x C))
                ((x, t₀) :: tail)) := by
      apply List.map_congr_left
      intro tail _
      rw [hSource₀]
      exact
        (applyGroundSubstitution_cons_prenexMatrix_all
          C x t₀ tail hxNotBound).symm
    rw [hLeaves₀] at hFlattening₀
    have hFlatteningRest :=
      cInstanceGroundSubstitutionPathsList_flattening
        x C hBodyUniversal hBodyDistinct hxNotBound
        tsRest hsRest hWFRest
        h₀.toFormula
        ((cInstanceGroundSubstitutionPaths h₀).map
          (fun tail =>
            applyGroundSubstitution
              (prenexMatrix (FormulaN.all x C))
              ((x, t₀) :: tail)))
        hFlattening₀
    simpa [CInstance.toFormula, CInstance.source,
      cInstanceGroundSubstitutionPaths,
      List.map_append, List.map_map,
      Function.comp_def] using
      hFlatteningRest

private theorem cInstanceGroundSubstitutionPathsList_flattening
    {L : Language} (x : Nat) (C : FormulaN L)
    (hBodyUniversal : UniversalPrenexFormula C)
    (hBodyDistinct : distinctQuantifierBindings C)
    (hxNotBound : ¬x ∈ formulaBVN C) :
    ∀ (ts : List (Term L)) (hs : List (CInstance L)),
      CInstance.WellFormedList x C ts hs →
      ∀ (init : FormulaN L) (initLeaves : List (FormulaN L)),
        ConjunctionFlattening init initLeaves →
        ConjunctionFlattening
          ((hs.map CInstance.toFormula).foldr
            (fun f rest first => FormulaN.conj first (rest f)) id init)
          (initLeaves ++ (cInstanceGroundSubstitutionPathsList x ts hs).map
            (fun path => applyGroundSubstitution
              (prenexMatrix (FormulaN.all x C)) path))
  | [], [], _, init, initLeaves, hInit => by
    simpa [cInstanceGroundSubstitutionPathsList] using hInit
  | [], _ :: _, hWF, _, _, _ => by exact hWF.elim
  | _ :: _, [], hWF, _, _, _ => by exact hWF.elim
  | t :: tsRest, h :: hsRest, hWF, init, initLeaves, hInit => by
    simp only [CInstance.WellFormedList] at hWF
    obtain ⟨hSource, hWFHead, hWFTail⟩ := hWF
    have hChildUniversal : UniversalPrenexFormula h.source := by
      rw [hSource]
      exact universalPrenexFormula_formulaSubstN C t x hBodyUniversal
    have hChildDistinct : distinctQuantifierBindings h.source := by
      rw [hSource]
      exact Herbrand.distinctQuantifierBindings_of_formulaSubstN C t x hBodyDistinct
    have hHead := cInstanceGroundSubstitutionPaths_flattening
      h hWFHead hChildUniversal hChildDistinct
    rw [hSource] at hHead
    simp only [← applyGroundSubstitution_cons_prenexMatrix_all
      C x t (hx := hxNotBound)] at hHead
    let leaves := (cInstanceGroundSubstitutionPaths h).map (fun tail =>
      applyGroundSubstitution (prenexMatrix (FormulaN.all x C)) ((x, t) :: tail))
    have hTail := cInstanceGroundSubstitutionPathsList_flattening
      x C hBodyUniversal hBodyDistinct hxNotBound tsRest hsRest hWFTail
      h.toFormula leaves hHead
    simpa [cInstanceGroundSubstitutionPathsList, leaves,
      List.map_append, List.map_map, List.append_assoc, Function.comp_def] using
      ConjunctionFlattening.conj hInit hTail

end /- ATTACH-BLOCKER: mutual -/

/-- The proof-coupled ground matrix instances encoded by a well-formed
`CInstance`, in exact path order and with multiplicity preserved. At each
universal node the first child's paths precede every remaining child's
paths, matching the right-nested output. Each path includes every prefix
binder, including vacuous binders, and carries closed terms and a closed
matrix leaf. A quantifier-free source contributes one empty substitution. -/
def cInstance_groundMatrixInstances {L : Language}
    (ci : CInstance L)
    (hWF : CInstance.WellFormed ci)
    (hUniversal : UniversalPrenexFormula ci.source)
    (hDistinct : distinctQuantifierBindings ci.source)
    (hSourceClosed : FormulaN.isClosed ci.source) :
    List (GroundMatrixInstance ci.source) :=
  (cInstanceGroundSubstitutionPaths ci).attach.map
    (fun path =>
      let hComplete :=
        cInstanceGroundSubstitutionPaths_complete
          ci hWF hUniversal path.1 path.2
      let hTermsClosed :=
        cInstanceGroundSubstitutionPaths_termsClosed
          ci path.1 path.2
      { substitution := path.1
        complete := hComplete
        termsClosed := hTermsClosed
        leafClosed :=
          applyGroundSubstitution_isClosed_of_fullPrefix
            ci.source path.1 hComplete hTermsClosed
            hSourceClosed hUniversal hDistinct }) /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

private theorem cInstance_groundMatrixInstances_toFormula
    {L : Language}
    (ci : CInstance L)
    (hWF : CInstance.WellFormed ci)
    (hUniversal : UniversalPrenexFormula ci.source)
    (hDistinct : distinctQuantifierBindings ci.source)
    (hSourceClosed : FormulaN.isClosed ci.source) :
    (cInstance_groundMatrixInstances
        ci hWF hUniversal hDistinct hSourceClosed).map
        GroundMatrixInstance.toFormula =
      (cInstanceGroundSubstitutionPaths ci).map
        (fun path =>
          applyGroundSubstitution
            (prenexMatrix ci.source) path) := by
  simpa [cInstance_groundMatrixInstances,
    GroundMatrixInstance.toFormula, List.map_map] using
    (List.attach_map_val
      (l := cInstanceGroundSubstitutionPaths ci)
      (f := fun path =>
        applyGroundSubstitution
          (prenexMatrix ci.source) path)) /- ATTACH-BLOCKER: private declaration -/

/-- A well-formed c-instance of a closed universal-prenex NNF source is
structurally a finite conjunction of complete ground instances of the
source matrix. The flattening follows each universal node's right-nested
output while retaining the ground-path order and repeated leaves. It does
not reassociate the entire output into one global chain. Quantifier-free
sources contribute their entire matrix as one leaf, even when that matrix
is itself a conjunction. -/
theorem cInstance_toFormula_isFiniteGroundConjunctionOfMatrix
    {L : Language}
    (ci : CInstance L)
    (hWF : CInstance.WellFormed ci)
    (hUniversal : UniversalPrenexFormula ci.source)
    (hNNF : FormulaN.isNNF ci.source)
    (hDistinct : distinctQuantifierBindings ci.source)
    (hSourceClosed : FormulaN.isClosed ci.source) :
    isFiniteGroundConjunctionOfMatrix
      ci.toFormula ci.source := by
  refine
    ⟨hUniversal, hNNF, hDistinct,
      cInstance_groundMatrixInstances
        ci hWF hUniversal hDistinct hSourceClosed, ?_⟩
  rw [cInstance_groundMatrixInstances_toFormula
    ci hWF hUniversal hDistinct hSourceClosed]
  exact
    cInstanceGroundSubstitutionPaths_flattening
      ci hWF hUniversal hDistinct /- ATTACH-BLOCKER: private name in relocated declaration -/

open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem

/- Enumerate every complete universal-instantiation path in a
c-instance.  Non-`forallInst` nodes contribute the unique empty path;
at a universal node every parallel witness branch is retained. -/

end LCS.Herbrand.SHGTheorem.Main
end
