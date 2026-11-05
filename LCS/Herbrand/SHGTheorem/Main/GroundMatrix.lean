import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand
import LCS.Herbrand.SHGTheorem.Main.SkolemSemanticsBase
import LCS.Herbrand.SHGTheorem.Main.SkolemEquisatisfiability
import LCS.Herbrand.SHGTheorem.Main.SHG
import Attach
import LCS.Herbrand.SHGTheorem.Main.GroundMatrix.ProofsStamp

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

end LCS.Herbrand.SHGTheorem.Main
end

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
namespace GroundMatrixCarrierRegression

private inductive Pred : Type where
  | unary /- ATTACH-BLOCKER: private declaration -/

private inductive Const : Type where
  | c /- ATTACH-BLOCKER: private declaration -/

def language : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Const
  predSymbols := Pred
  predArity := fun _ => 1
  hasEquality := false /- ATTACH-BLOCKER: private name in relocated declaration -/

private def constant : Term language :=
  .const .c /- ATTACH-BLOCKER: private declaration -/

private def unaryAtom (t : Term language) : FormulaN language :=
  .predN .unary (fun _ => t) /- ATTACH-BLOCKER: private declaration -/

def atom : FormulaN language :=
  unaryAtom constant /- ATTACH-BLOCKER: private name in relocated declaration -/

private theorem constant_closed :
    Term.isClosed constant := by
  rfl /- ATTACH-BLOCKER: private declaration -/

private theorem unaryAtom_fv (t : Term language) :
    formulaFVN (unaryAtom t) = termFV t := by
  funext x
  apply propext
  change (∃ _ : Fin 1, termFV t x) ↔ termFV t x
  constructor
  · rintro ⟨_, hx⟩
    exact hx
  · intro hx
    exact ⟨⟨0, Nat.zero_lt_succ 0⟩, hx⟩ /- ATTACH-BLOCKER: private declaration -/

private theorem unaryAtom_constant_closed :
    FormulaN.isClosed (unaryAtom constant) := by
  unfold FormulaN.isClosed
  rw [unaryAtom_fv]
  exact constant_closed /- ATTACH-BLOCKER: private declaration -/

private theorem atom_closed :
    FormulaN.isClosed atom := by
  simpa only [atom] using unaryAtom_constant_closed /- ATTACH-BLOCKER: private declaration -/

private def unarySource : FormulaN language :=
  .all 0 (unaryAtom (.var 0)) /- ATTACH-BLOCKER: private declaration -/

private def qfSource : FormulaN language :=
  atom /- ATTACH-BLOCKER: private declaration -/

private def twoPrefixSource : FormulaN language :=
  .all 0 (.all 1 atom) /- ATTACH-BLOCKER: private declaration -/

private def conjunctiveSource : FormulaN language :=
  .all 0 (.conj (unaryAtom (.var 0)) (unaryAtom (.var 0))) /- ATTACH-BLOCKER: private declaration -/

private def residualSource : FormulaN language :=
  .all 0 (.conj (unaryAtom (.var 0)) (unaryAtom (.var 1))) /- ATTACH-BLOCKER: private declaration -/

private def existentialSource : FormulaN language :=
  .ex 0 atom /- ATTACH-BLOCKER: private declaration -/

private def nonPrenexSource : FormulaN language :=
  .conj (.all 0 atom) atom /- ATTACH-BLOCKER: private declaration -/

private def nonNnfSource : FormulaN language :=
  .all 0 (.impl (unaryAtom (.var 0)) (unaryAtom (.var 0))) /- ATTACH-BLOCKER: private declaration -/

private def repeatedBinderSource : FormulaN language :=
  .all 0 (.all 0 atom) /- ATTACH-BLOCKER: private declaration -/

private theorem unarySource_universalPrenex :
    LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula
      unarySource := by
  simp [LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula,
    unarySource, unaryAtom, LCS.Herbrand.PrenexForm.isPrenex,
    LCS.Herbrand.PrenexForm.prenexPrefix,
    FirstOrder.SemanticsN.isQuantifierFree] /- ATTACH-BLOCKER: private declaration -/

private theorem unarySource_distinct :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      unarySource := by
  simp [unarySource, unaryAtom,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaBVN] /- ATTACH-BLOCKER: private declaration -/

private theorem unarySource_nnf :
    FormulaN.isNNF unarySource := by
  simp [unarySource, unaryAtom, FormulaN.isNNF] /- ATTACH-BLOCKER: private declaration -/

private theorem qfSource_universalPrenex :
    LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula
      qfSource := by
  simp [LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula,
    qfSource, atom, unaryAtom, LCS.Herbrand.PrenexForm.isPrenex,
    LCS.Herbrand.PrenexForm.prenexPrefix,
    FirstOrder.SemanticsN.isQuantifierFree] /- ATTACH-BLOCKER: private declaration -/

private theorem qfSource_distinct :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      qfSource := by
  simp [qfSource, atom, unaryAtom,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings] /- ATTACH-BLOCKER: private declaration -/

private theorem qfSource_nnf :
    FormulaN.isNNF qfSource := by
  simp [qfSource, atom, unaryAtom, FormulaN.isNNF] /- ATTACH-BLOCKER: private declaration -/

private theorem twoPrefixSource_universalPrenex :
    LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula
      twoPrefixSource := by
  simp [LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula,
    twoPrefixSource, atom, unaryAtom,
    LCS.Herbrand.PrenexForm.isPrenex,
    LCS.Herbrand.PrenexForm.prenexPrefix,
    FirstOrder.SemanticsN.isQuantifierFree] /- ATTACH-BLOCKER: private declaration -/

private theorem twoPrefixSource_distinct :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      twoPrefixSource := by
  simp [twoPrefixSource, atom, unaryAtom,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaBVN] /- ATTACH-BLOCKER: private declaration -/

private theorem twoPrefixSource_nnf :
    FormulaN.isNNF twoPrefixSource := by
  simp [twoPrefixSource, atom, unaryAtom, FormulaN.isNNF] /- ATTACH-BLOCKER: private declaration -/

private theorem conjunctiveSource_universalPrenex :
    LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula
      conjunctiveSource := by
  simp [LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula,
    conjunctiveSource, unaryAtom, LCS.Herbrand.PrenexForm.isPrenex,
    LCS.Herbrand.PrenexForm.prenexPrefix,
    FirstOrder.SemanticsN.isQuantifierFree] /- ATTACH-BLOCKER: private declaration -/

private theorem conjunctiveSource_distinct :
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings
      conjunctiveSource := by
  simp [conjunctiveSource, unaryAtom,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaBVN] /- ATTACH-BLOCKER: private declaration -/

private theorem conjunctiveSource_nnf :
    FormulaN.isNNF conjunctiveSource := by
  simp [conjunctiveSource, unaryAtom, FormulaN.isNNF] /- ATTACH-BLOCKER: private declaration -/

private def unaryInstance : GroundMatrixInstance unarySource where
  substitution := [(0, constant)]
  complete := by rfl
  termsClosed := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact constant_closed
  leafClosed := by
    change FormulaN.isClosed (unaryAtom constant)
    exact unaryAtom_constant_closed /- ATTACH-BLOCKER: private declaration -/

private theorem unaryInstance_formula :
    unaryInstance.toFormula = unaryAtom constant := by
  rfl /- ATTACH-BLOCKER: private declaration -/

private def qfInstance : GroundMatrixInstance qfSource where
  substitution := []
  complete := by rfl
  termsClosed := by
    simp
  leafClosed := by
    change FormulaN.isClosed atom
    exact atom_closed /- ATTACH-BLOCKER: private declaration -/

private theorem qfInstance_formula :
    qfInstance.toFormula = atom := by
  rfl /- ATTACH-BLOCKER: private declaration -/

private def twoPrefixInstance :
    GroundMatrixInstance twoPrefixSource where
  substitution := [(0, constant), (1, constant)]
  complete := by rfl
  termsClosed := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact constant_closed
    · exact constant_closed
  leafClosed := by
    change FormulaN.isClosed atom
    exact atom_closed /- ATTACH-BLOCKER: private declaration -/

private theorem twoPrefixInstance_formula :
    twoPrefixInstance.toFormula = atom := by
  rfl /- ATTACH-BLOCKER: private declaration -/

private def conjunctiveInstance :
    GroundMatrixInstance conjunctiveSource where
  substitution := [(0, constant)]
  complete := by rfl
  termsClosed := by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact constant_closed
  leafClosed := by
    change FormulaN.isClosed
      (.conj (unaryAtom constant) (unaryAtom constant))
    have hConstant : termFV constant = (∅ : Set Nat) :=
      constant_closed
    simp [FormulaN.isClosed, formulaFVN, unaryAtom_fv, hConstant] /- ATTACH-BLOCKER: private declaration -/

private theorem conjunctiveInstance_formula :
    conjunctiveInstance.toFormula =
      FormulaN.conj
        (unaryAtom constant) (unaryAtom constant) := by
  rfl /- ATTACH-BLOCKER: private declaration -/

/-- A complete singleton substitution turns `∀x P(x)` into `P(c)`. -/
example :
    isFiniteGroundConjunctionOfMatrix
      (unaryAtom constant) unarySource := by
  refine
    ⟨unarySource_universalPrenex, unarySource_nnf, unarySource_distinct,
      ⟨[unaryInstance], ?_⟩⟩
  simpa only [List.map_cons, List.map_nil, unaryInstance_formula] using
    ConjunctionFlattening.leaf (unaryAtom constant) /- ATTACH-BLOCKER: unsupported untagged example -/

/-- A closed quantifier-free source has an empty prefix, whose exact
complete substitution is the empty list. -/
example :
    isFiniteGroundConjunctionOfMatrix atom qfSource := by
  refine
    ⟨qfSource_universalPrenex, qfSource_nnf, qfSource_distinct,
      ⟨[qfInstance], ?_⟩⟩
  simpa only [List.map_cons, List.map_nil, qfInstance_formula] using
    ConjunctionFlattening.leaf atom /- ATTACH-BLOCKER: unsupported untagged example -/

/-- Omitting a required prefix key cannot construct an instance. -/
example :
    ¬ ∃ g : GroundMatrixInstance unarySource,
        g.substitution = [] := by
  rintro ⟨g, hSubstitution⟩
  have hComplete := g.complete
  simp [hSubstitution, unarySource, unaryAtom,
    LCS.Herbrand.PrenexForm.prenexPrefix] at hComplete /- ATTACH-BLOCKER: unsupported untagged example -/

/-- Adding a key beyond the source prefix cannot construct an instance. -/
example :
    ¬ ∃ g : GroundMatrixInstance unarySource,
        g.substitution =
          [(0, constant), (1, constant)] := by
  rintro ⟨g, hSubstitution⟩
  have hComplete := g.complete
  simp [hSubstitution, unarySource, unaryAtom,
    LCS.Herbrand.PrenexForm.prenexPrefix] at hComplete /- ATTACH-BLOCKER: unsupported untagged example -/

/-- A key different from the bound prefix variable is rejected. -/
example :
    ¬ ∃ g : GroundMatrixInstance unarySource,
        g.substitution = [(1, constant)] := by
  rintro ⟨g, hSubstitution⟩
  have hComplete := g.complete
  simp [hSubstitution, unarySource,
    LCS.Herbrand.PrenexForm.prenexPrefix] at hComplete /- ATTACH-BLOCKER: unsupported untagged example -/

/-- Complete keys in the wrong order are rejected. -/
example :
    ¬ ∃ g : GroundMatrixInstance twoPrefixSource,
        g.substitution =
          [(1, constant), (0, constant)] := by
  rintro ⟨g, hSubstitution⟩
  have hComplete := g.complete
  simp [hSubstitution, twoPrefixSource,
    LCS.Herbrand.PrenexForm.prenexPrefix] at hComplete /- ATTACH-BLOCKER: unsupported untagged example -/

/-- A replacement term containing a variable is rejected even when its
key is correct. -/
example :
    ¬ ∃ g : GroundMatrixInstance unarySource,
        g.substitution = [(0, Term.var 1)] := by
  rintro ⟨g, hSubstitution⟩
  have hMember :
      (0, Term.var 1) ∈ g.substitution := by
    rw [hSubstitution]
    exact List.mem_cons_self
  have hClosed := g.termsClosed (0, Term.var 1) hMember
  have hFree : 1 ∈ termFV (Term.var 1 : Term language) := rfl
  rw [hClosed] at hFree
  exact hFree /- ATTACH-BLOCKER: unsupported untagged example -/

/-- Exact prefix coverage still rejects a matrix leaf with a residual
free variable outside the prefix. -/
example :
    ¬ ∃ g : GroundMatrixInstance residualSource,
        g.substitution = [(0, constant)] := by
  rintro ⟨g, hSubstitution⟩
  have hClosed := g.leafClosed
  rw [hSubstitution] at hClosed
  change FormulaN.isClosed
    (.conj (unaryAtom constant) (unaryAtom (.var 1))) at hClosed
  have hFree :
      1 ∈ formulaFVN
        (.conj (unaryAtom constant) (unaryAtom (.var 1))) := by
    change
      1 ∈ formulaFVN (unaryAtom constant) ∪
        formulaFVN (unaryAtom (.var 1))
    apply Or.inr
    rw [unaryAtom_fv]
    rfl
  rw [hClosed] at hFree
  exact hFree /- ATTACH-BLOCKER: unsupported untagged example -/

/-- An existential prefix is not a universal-prenex source. -/
example :
    ¬ isFiniteGroundConjunctionOfMatrix atom existentialSource := by
  intro h
  have hUniversal := h.1
  simp [LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula,
    existentialSource, atom, unaryAtom,
    LCS.Herbrand.PrenexForm.isPrenex,
    LCS.Herbrand.PrenexForm.prenexPrefix,
    FirstOrder.SemanticsN.isQuantifierFree] at hUniversal /- ATTACH-BLOCKER: unsupported untagged example -/

/-- A quantifier below a connective is not a prenex source. -/
example :
    ¬ isFiniteGroundConjunctionOfMatrix atom nonPrenexSource := by
  intro h
  have hPrenex := h.1.1
  simp [nonPrenexSource, atom, unaryAtom,
    LCS.Herbrand.PrenexForm.isPrenex,
    FirstOrder.SemanticsN.isQuantifierFree] at hPrenex /- ATTACH-BLOCKER: unsupported untagged example -/

/-- Reusing the same bound-variable name at two prefix positions violates
the distinct-binding invariant. -/
example :
    ¬ isFiniteGroundConjunctionOfMatrix atom repeatedBinderSource := by
  intro h
  have hDistinct := h.2.2.1
  simp [repeatedBinderSource, atom, unaryAtom,
    LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings,
    formulaBVN] at hDistinct /- ATTACH-BLOCKER: unsupported untagged example -/

/-- A universal-prenex formula with a quantifier-free but non-NNF matrix
is outside the corollary's NNF domain. -/
example :
    ¬ isFiniteGroundConjunctionOfMatrix
      (.impl atom atom) nonNnfSource := by
  intro h
  have hNNF := h.2.1
  simp [nonNnfSource, unaryAtom, FormulaN.isNNF] at hNNF /- ATTACH-BLOCKER: unsupported untagged example -/

/-- The flattening relation has no empty-family constructor. -/
example {L : Language} {F B : FormulaN L} :
    ¬ ConjunctionFlattening F
      (([] : List (GroundMatrixInstance B)).map
        GroundMatrixInstance.toFormula) := by
  intro h
  exact h.nonempty rfl /- ATTACH-BLOCKER: unsupported untagged example -/

/-- Left-associated conjunctions are accepted. Repeating the same
instance also confirms that repeated terms, substitutions, and leaves are
all permitted. -/
example :
    isFiniteGroundConjunctionOfMatrix
      (.conj (.conj atom atom) atom) twoPrefixSource := by
  refine
    ⟨twoPrefixSource_universalPrenex, twoPrefixSource_nnf,
      twoPrefixSource_distinct,
      ⟨[twoPrefixInstance, twoPrefixInstance, twoPrefixInstance], ?_⟩⟩
  simpa [twoPrefixInstance_formula] using
    ConjunctionFlattening.conj
      (ConjunctionFlattening.conj
        (ConjunctionFlattening.leaf atom)
        (ConjunctionFlattening.leaf atom))
      (ConjunctionFlattening.leaf atom) /- ATTACH-BLOCKER: unsupported untagged example -/

/-- The same ordered leaf list is also accepted with right-associated
conjunctions. -/
example :
    isFiniteGroundConjunctionOfMatrix
      (.conj atom (.conj atom atom)) twoPrefixSource := by
  refine
    ⟨twoPrefixSource_universalPrenex, twoPrefixSource_nnf,
      twoPrefixSource_distinct,
      ⟨[twoPrefixInstance, twoPrefixInstance, twoPrefixInstance], ?_⟩⟩
  simpa [twoPrefixInstance_formula] using
    ConjunctionFlattening.conj
      (ConjunctionFlattening.leaf atom)
      (ConjunctionFlattening.conj
        (ConjunctionFlattening.leaf atom)
        (ConjunctionFlattening.leaf atom)) /- ATTACH-BLOCKER: unsupported untagged example -/

/-- A conjunctive matrix instance remains one leaf rather than being
blindly split at its root conjunction. -/
example :
    isFiniteGroundConjunctionOfMatrix
      (.conj (unaryAtom constant) (unaryAtom constant))
      conjunctiveSource := by
  refine
    ⟨conjunctiveSource_universalPrenex, conjunctiveSource_nnf,
      conjunctiveSource_distinct,
      ⟨[conjunctiveInstance], ?_⟩⟩
  simpa only [List.map_cons, List.map_nil,
    conjunctiveInstance_formula] using
    ConjunctionFlattening.leaf
      (.conj (unaryAtom constant) (unaryAtom constant)) /- ATTACH-BLOCKER: unsupported untagged example -/

/-- Double negation is semantically equivalent to the leaf, but that
semantic fact cannot masquerade as conjunction syntax. -/
example :
    LCS.FirstOrder.Semantics.Equivalence.foLogEquivN
        (.neg (.neg atom)) atom ∧
      ¬ ConjunctionFlattening (.neg (.neg atom)) [atom] := by
  constructor
  · exact
      LCS.FirstOrder.Semantics.Equivalence.foLogEquivN_double_neg atom
  · intro h
    cases h /- ATTACH-BLOCKER: unsupported untagged example -/

end GroundMatrixCarrierRegression
end LCS.Herbrand.SHGTheorem.Main
end

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
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.NNFHauptsatz.Theorem

private theorem liftFormulaSkolem_isQuantifierFree {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (A : FormulaN L)
    (hQF : FirstOrder.SemanticsN.isQuantifierFree A) :
    FirstOrder.SemanticsN.isQuantifierFree
      (liftFormulaSkolem (skolemRank := skolemRank) A) := by
  induction A with
  | predN _ _ => trivial
  | eq_ _ _ _ => trivial
  | neg A ih => exact ih hQF
  | conj A B ihA ihB =>
    exact ⟨ihA hQF.1, ihB hQF.2⟩
  | disj A B ihA ihB =>
    exact ⟨ihA hQF.1, ihB hQF.2⟩
  | impl A B ihA ihB =>
    exact ⟨ihA hQF.1, ihB hQF.2⟩
  | all _ _ => exact hQF.elim
  | ex _ _ => exact hQF.elim /- ATTACH-BLOCKER: private declaration -/

private theorem liftFormulaSkolem_isPrenex {L : Language}
    {n : Nat} {skolemRank : Fin n → Nat}
    (A : FormulaN L) (hPrenex : isPrenex A) :
    isPrenex
      (liftFormulaSkolem (skolemRank := skolemRank) A) := by
  induction A with
  | predN _ _ =>
    exact hPrenex
  | eq_ _ _ _ =>
    exact hPrenex
  | neg A _ =>
    exact liftFormulaSkolem_isQuantifierFree (.neg A) hPrenex
  | conj A B _ _ =>
    exact liftFormulaSkolem_isQuantifierFree (.conj A B) hPrenex
  | disj A B _ _ =>
    exact liftFormulaSkolem_isQuantifierFree (.disj A B) hPrenex
  | impl A B _ _ =>
    exact liftFormulaSkolem_isQuantifierFree (.impl A B) hPrenex
  | all _ A ih =>
    exact ih hPrenex
  | ex _ A ih =>
    exact ih hPrenex /- ATTACH-BLOCKER: private declaration -/

private theorem isQuantifierFree_descriptorCount_zero {L : Language}
    (A : FormulaN L)
    (hQF : FirstOrder.SemanticsN.isQuantifierFree A) :
    skolemDescriptorCount A = 0 := by
  induction A with
  | predN _ _ => rfl
  | eq_ _ _ _ => rfl
  | neg _ _ =>
    rfl
  | conj A B ihA ihB =>
    simp [skolemDescriptorCount, ihA hQF.1, ihB hQF.2]
  | disj A B ihA ihB =>
    simp [skolemDescriptorCount, ihA hQF.1, ihB hQF.2]
  | impl _ _ _ _ =>
    rfl
  | all _ _ =>
    exact hQF.elim
  | ex _ _ =>
    exact hQF.elim /- ATTACH-BLOCKER: private declaration -/

/-- Exact Skolem traversal preserves prenex form and removes every
existential from a prenex input.  The index-length hypothesis rules out
malformed arbitrary traversal states. -/
private theorem skolemFormExactAux_universalPrenex {L : Language}
    (spec : SkolemSpec L) :
    ∀ (m : Nat) (A : FormulaN spec.language) (scope : List Nat)
      (indices : List (Fin spec.n)) (B : FormulaN spec.language)
      (used : Nat),
      formulaQuantCount A = m →
      isPrenex A →
      indices.length = skolemDescriptorCount A →
      skolemFormExactAux spec A scope indices = some (B, used) →
      UniversalPrenexFormula B := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro A scope indices B used hCount hPrenex hLength hRun
    cases A with
    | predN P ts =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      simp only [skolemFormExactAux] at hRun
      cases hRun
      exact ⟨trivial, by
        intro p hp
        simp [prenexPrefix] at hp⟩
    | eq_ hEq t₁ t₂ =>
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (by
          simpa [skolemDescriptorCount] using hLength)
      subst indices
      simp only [skolemFormExactAux] at hRun
      cases hRun
      exact ⟨trivial, by
        intro p hp
        simp [prenexPrefix] at hp⟩
    | neg C =>
      have hQF :
          FirstOrder.SemanticsN.isQuantifierFree (FormulaN.neg C) :=
        hPrenex
      have hZero :=
        isQuantifierFree_descriptorCount_zero (.neg C) hQF
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (hLength.trans hZero)
      subst indices
      have hSelf :=
        skolemFormExactAux_eq_self_of_descriptorCount_zero
          spec (.neg C) scope hZero
      have hEq : B = FormulaN.neg C :=
        skolemFormExactAux_formula_unique hRun hSelf
      subst B
      exact ⟨hQF, by
        intro p hp
        simp [prenexPrefix] at hp⟩
    | conj C D =>
      have hQF :
          FirstOrder.SemanticsN.isQuantifierFree (FormulaN.conj C D) :=
        hPrenex
      have hZero :=
        isQuantifierFree_descriptorCount_zero (.conj C D) hQF
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (hLength.trans hZero)
      subst indices
      have hSelf :=
        skolemFormExactAux_eq_self_of_descriptorCount_zero
          spec (.conj C D) scope hZero
      have hEq : B = FormulaN.conj C D :=
        skolemFormExactAux_formula_unique hRun hSelf
      subst B
      exact ⟨hQF, by
        intro p hp
        simp [prenexPrefix] at hp⟩
    | disj C D =>
      have hQF :
          FirstOrder.SemanticsN.isQuantifierFree (FormulaN.disj C D) :=
        hPrenex
      have hZero :=
        isQuantifierFree_descriptorCount_zero (.disj C D) hQF
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (hLength.trans hZero)
      subst indices
      have hSelf :=
        skolemFormExactAux_eq_self_of_descriptorCount_zero
          spec (.disj C D) scope hZero
      have hEq : B = FormulaN.disj C D :=
        skolemFormExactAux_formula_unique hRun hSelf
      subst B
      exact ⟨hQF, by
        intro p hp
        simp [prenexPrefix] at hp⟩
    | impl C D =>
      have hQF :
          FirstOrder.SemanticsN.isQuantifierFree (FormulaN.impl C D) :=
        hPrenex
      have hZero :=
        isQuantifierFree_descriptorCount_zero (.impl C D) hQF
      have hNil : indices = [] :=
        List.length_eq_zero_iff.mp (hLength.trans hZero)
      subst indices
      have hSelf :=
        skolemFormExactAux_eq_self_of_descriptorCount_zero
          spec (.impl C D) scope hZero
      have hEq : B = FormulaN.impl C D :=
        skolemFormExactAux_formula_unique hRun hSelf
      subst B
      exact ⟨hQF, by
        intro p hp
        simp [prenexPrefix] at hp⟩
    | all x C =>
      have hCountC : formulaQuantCount C < m := by
        simp [formulaQuantCount] at hCount
        omega
      have hLengthC :
          indices.length = skolemDescriptorCount C := by
        simpa [skolemDescriptorCount] using hLength
      have hRunTop := hRun
      simp only [skolemFormExactAux] at hRun
      generalize hRec :
          skolemFormExactAux spec C (scope ++ [x]) indices = rec
        at hRun
      cases rec with
      | none =>
        simp at hRun
      | some result =>
        obtain ⟨C', used'⟩ := result
        have hWrapped :
            skolemFormExactAux spec (FormulaN.all x C) scope indices =
              some (FormulaN.all x C', used') := by
          simp [skolemFormExactAux, hRec]
        have hB : B = FormulaN.all x C' :=
          skolemFormExactAux_formula_unique hRunTop hWrapped
        subst B
        have hC' :=
          ih (formulaQuantCount C) hCountC C (scope ++ [x])
            indices C' used' rfl hPrenex hLengthC hRec
        refine ⟨hC'.1, ?_⟩
        intro p hp
        change
          p ∈ (QuantifierKind.universal, x) :: prenexPrefix C' at hp
        rcases List.mem_cons.mp hp with rfl | hp
        · rfl
        · exact hC'.2 p hp
    | ex x C =>
      cases indices with
      | nil =>
        have hImpossible :
            0 = 1 + skolemDescriptorCount C := by
          simpa only [List.length_nil, skolemDescriptorCount] using hLength
        omega
      | cons i rest =>
        have hCountSub :
            formulaQuantCount
                (formulaSubstN C (exactSkolemTerm spec i) x) < m := by
          rw [formulaSubst_quantCount]
          simp [formulaQuantCount] at hCount
          omega
        have hLengthRest :
            rest.length =
              skolemDescriptorCount
                (formulaSubstN C (exactSkolemTerm spec i) x) := by
          rw [formulaSubstN_descriptorCount]
          simp only [List.length_cons, skolemDescriptorCount] at hLength
          omega
        have hPrenexSub :
            isPrenex
              (formulaSubstN C (exactSkolemTerm spec i) x) :=
          isPrenex_formulaSubstN C (exactSkolemTerm spec i) x hPrenex
        have hRunTop := hRun
        simp only [skolemFormExactAux, skolemSubst] at hRun
        generalize hRec :
            skolemFormExactAux spec
              (formulaSubstN C (exactSkolemTerm spec i) x)
              scope rest = rec at hRun
        cases rec with
        | none =>
          simp at hRun
        | some result =>
          obtain ⟨C', used'⟩ := result
          have hWrapped :
              skolemFormExactAux spec (FormulaN.ex x C) scope (i :: rest) =
                some (C', used' + 1) := by
            simp [skolemFormExactAux, skolemSubst, hRec]
          have hB : B = C' :=
            skolemFormExactAux_formula_unique hRunTop hWrapped
          subst B
          exact ih _ hCountSub _ scope rest C' used' rfl
            hPrenexSub hLengthRest hRec /- ATTACH-BLOCKER: private declaration -/

/- Enumerate every complete universal-instantiation path in a
c-instance.  Non-`forallInst` nodes contribute the unique empty path;
at a universal node every parallel witness branch is retained. -/
mutual
def shgPrenexGroundSubstitutions {L : Language} :
    CInstance L → List (List (Nat × Term L))
  | .forallInst x _ t₀ h₀ tsRest hsRest _ _ =>
    (shgPrenexGroundSubstitutions h₀).map
        (fun path => (x, t₀) :: path) ++
      shgPrenexGroundSubstitutionsList x tsRest hsRest
  | _ => [[]]

def shgPrenexGroundSubstitutionsList {L : Language}
    (x : Nat) :
    List (Term L) → List (CInstance L) →
      List (List (Nat × Term L))
  | [], _ => []
  | _ :: _, [] => []
  | t :: tsRest, h :: hsRest =>
    (shgPrenexGroundSubstitutions h).map
        (fun path => (x, t) :: path) ++
      shgPrenexGroundSubstitutionsList x tsRest hsRest
end /- ATTACH-BLOCKER: mutual -/

private theorem cInstanceGroundSubstitutions_ne_nil {L : Language} :
    ∀ ci : CInstance L, shgPrenexGroundSubstitutions ci ≠ []
  | .atom _ _ => by simp [shgPrenexGroundSubstitutions]
  | .negAtom _ _ => by simp [shgPrenexGroundSubstitutions]
  | .connective _ _ _ _ _ => by simp [shgPrenexGroundSubstitutions]
  | .forallInst x C t₀ h₀ tsRest hsRest hGround₀ hGroundRest => by
    have hHead := cInstanceGroundSubstitutions_ne_nil h₀
    cases hPaths : shgPrenexGroundSubstitutions h₀ with
    | nil =>
      exact absurd hPaths hHead
    | cons path paths =>
      simp [shgPrenexGroundSubstitutions, hPaths] /- ATTACH-BLOCKER: private declaration -/

mutual
theorem shgPrenexGroundSubstitutions_entries_closed
    {L : Language} :
    ∀ (ci : CInstance L)
      (entries : List (Nat × Term L)),
      entries ∈ shgPrenexGroundSubstitutions ci →
      ∀ p ∈ entries, Term.isClosed p.2
  | .atom _ _, entries, hEntries => by
    simp only [shgPrenexGroundSubstitutions,
      List.mem_singleton] at hEntries
    subst entries
    simp
  | .negAtom _ _, entries, hEntries => by
    simp only [shgPrenexGroundSubstitutions,
      List.mem_singleton] at hEntries
    subst entries
    simp
  | .connective _ _ _ _ _, entries, hEntries => by
    simp only [shgPrenexGroundSubstitutions,
      List.mem_singleton] at hEntries
    subst entries
    simp
  | .forallInst x C t₀ h₀ tsRest hsRest hGround₀ hGroundRest,
      entries, hEntries => by
    simp only [shgPrenexGroundSubstitutions, List.mem_append,
      List.mem_map] at hEntries
    rcases hEntries with ⟨path, hPath, rfl⟩ | hRest
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hGround₀
      · exact shgPrenexGroundSubstitutions_entries_closed
          h₀ path hPath p hp
    · exact shgPrenexGroundSubstitutionsList_entries_closed
        x tsRest hsRest hGroundRest entries hRest

theorem shgPrenexGroundSubstitutionsList_entries_closed
    {L : Language} (x : Nat) :
    ∀ (ts : List (Term L)) (hs : List (CInstance L)),
      (∀ t ∈ ts, Term.isClosed t) →
      ∀ entries ∈ shgPrenexGroundSubstitutionsList x ts hs,
        ∀ p ∈ entries, Term.isClosed p.2
  | [], _, _, entries, hEntries => by
    simp [shgPrenexGroundSubstitutionsList] at hEntries
  | _ :: _, [], _, entries, hEntries => by
    simp [shgPrenexGroundSubstitutionsList] at hEntries
  | t :: tsRest, h :: hsRest, hGround, entries, hEntries => by
    simp only [shgPrenexGroundSubstitutionsList, List.mem_append,
      List.mem_map] at hEntries
    rcases hEntries with ⟨path, hPath, rfl⟩ | hRest
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hGround t List.mem_cons_self
      · exact shgPrenexGroundSubstitutions_entries_closed
          h path hPath p hp
    · exact shgPrenexGroundSubstitutionsList_entries_closed
        x tsRest hsRest
        (fun t' ht' =>
          hGround t' (List.mem_cons_of_mem _ ht'))
        entries hRest
end /- ATTACH-BLOCKER: mutual -/

private theorem formulaEvalN_foldl_conj_iff {L : Language}
    (M : Structure L) (s : Assignment M)
    (init : FormulaN L) (fs : List (FormulaN L)) :
    formulaEvalN M
        (fs.foldl (fun acc f => FormulaN.conj acc f) init) s ↔
      formulaEvalN M init s ∧
        ∀ f ∈ fs, formulaEvalN M f s := by
  induction fs generalizing init with
  | nil => simp
  | cons f rest ih =>
    simp only [List.foldl_cons, ih]
    constructor
    · rintro ⟨⟨hInit, hf⟩, hRest⟩
      refine ⟨hInit, ?_⟩
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hf
      · exact hRest g hg
    · rintro ⟨hInit, hAll⟩
      exact ⟨⟨hInit, hAll f List.mem_cons_self⟩,
        fun g hg => hAll g (List.mem_cons_of_mem _ hg)⟩ /- ATTACH-BLOCKER: private declaration -/

/-- If every matrix instance along every complete path of a well-formed
c-instance evaluates to true, then its (possibly differently
parenthesized) c-instance formula evaluates to true. -/
private theorem cInstance_eval_of_groundSubstitutions {L : Language}
    (ci : CInstance L)
    (hWF : CInstance.WellFormed ci)
    (hUniversal : UniversalPrenexFormula ci.source)
    (hDistinct : distinctQuantifierBindings ci.source)
    (M : Structure L) (s : Assignment M) :
    (∀ path ∈ shgPrenexGroundSubstitutions ci,
        formulaEvalN M
          (applyGroundSubstitution (prenexMatrix ci.source) path) s) →
      formulaEvalN M ci.toFormula s := by
  cases ci with
  | atom B hAtom =>
    intro hPaths
    have hQF : FirstOrder.SemanticsN.isQuantifierFree B :=
      isAtomic_isQuantifierFree B hAtom
    have hMatrix :=
      isQuantifierFree_prenexMatrix_eq_self B hQF
    have hEval := hPaths [] (by
      simp [shgPrenexGroundSubstitutions])
    simpa only [CInstance.toFormula, CInstance.source,
      applyGroundSubstitution, List.foldl_nil, hMatrix] using hEval
  | negAtom B hAtom =>
    intro hPaths
    have hQF :
        FirstOrder.SemanticsN.isQuantifierFree (FormulaN.neg B) :=
      isAtomic_isQuantifierFree B hAtom
    have hMatrix :=
      isQuantifierFree_prenexMatrix_eq_self (.neg B) hQF
    have hEval := hPaths [] (by
      simp [shgPrenexGroundSubstitutions])
    simpa only [CInstance.toFormula, CInstance.source,
      applyGroundSubstitution, List.foldl_nil, hMatrix] using hEval
  | connective star C D H K =>
    intro hPaths
    have hQF :
        FirstOrder.SemanticsN.isQuantifierFree
          (CInstance.source (.connective star C D H K)) :=
      by
        cases star <;> exact hUniversal.1
    have hEq :=
      cInstance_toFormula_eq_source_of_qf
        (.connective star C D H K) hWF hQF
    have hMatrix :=
      isQuantifierFree_prenexMatrix_eq_self
        (CInstance.source (.connective star C D H K)) hQF
    rw [hEq]
    have hEval := hPaths [] (by
      simp [shgPrenexGroundSubstitutions])
    simpa only [applyGroundSubstitution, List.foldl_nil,
      hMatrix] using hEval
  | forallInst x C t₀ h₀ tsRest hsRest hGround₀ hGroundRest =>
    intro hPaths
    simp only [CInstance.WellFormed] at hWF
    obtain ⟨hSrc₀, hWF₀, hWFRest⟩ := hWF
    have hBodyUniversal :
        UniversalPrenexFormula C :=
      universalPrenexFormula_body_of_all C x hUniversal
    have hBodyDistinct : distinctQuantifierBindings C :=
      hDistinct.1
    have hxNotBV : ¬x ∈ formulaBVN C :=
      hDistinct.2
    have hUniversal₀ :
        UniversalPrenexFormula h₀.source := by
      rw [hSrc₀]
      exact universalPrenexFormula_formulaSubstN
        C t₀ x hBodyUniversal
    have hDistinct₀ :
        distinctQuantifierBindings h₀.source := by
      rw [hSrc₀]
      exact distinctQuantifierBindings_of_formulaSubstN
        C t₀ x hBodyDistinct
    simp only [CInstance.toFormula]
    have hFold : ∀ (fs : List (FormulaN L)) (first : FormulaN L),
        formulaEvalN M first s →
        (∀ f ∈ fs, formulaEvalN M f s) →
        formulaEvalN M
          (fs.foldr (fun f rest first => FormulaN.conj first (rest f)) id first) s := by
      intro fs
      induction fs with
      | nil => intro first hFirst _; exact hFirst
      | cons f fs ih =>
        intro first hFirst hFs
        exact ⟨hFirst, ih f (hFs f (by simp))
          (fun g hg => hFs g (List.mem_cons_of_mem f hg))⟩
    apply hFold
    · apply cInstance_eval_of_groundSubstitutions
        h₀ hWF₀ hUniversal₀ hDistinct₀ M s
      intro tail hTail
      rw [hSrc₀]
      rw [← applyGroundSubstitution_cons_prenexMatrix_all
        C x t₀ tail hxNotBV]
      apply hPaths ((x, t₀) :: tail)
      simp only [shgPrenexGroundSubstitutions,
        List.mem_append, List.mem_map]
      exact Or.inl ⟨tail, hTail, rfl⟩
    · intro f hf
      rw [List.mem_map] at hf
      obtain ⟨mappedChild, hMappedChild, rfl⟩ := hf
      have hEvalRest :
          ∀ (ts : List (Term L)) (hs : List (CInstance L)),
            CInstance.WellFormedList x C ts hs →
            (∀ entries ∈
                shgPrenexGroundSubstitutionsList x ts hs,
              formulaEvalN M
                (applyGroundSubstitution
                  (prenexMatrix (FormulaN.all x C)) entries) s) →
            ∀ child ∈ hs,
              formulaEvalN M child.toFormula s := by
        intro ts
        induction ts with
        | nil =>
          intro hs hWFList hEval targetChild hTarget
          cases hs with
          | nil => exact absurd hTarget (by simp)
          | cons _ _ =>
            simp [CInstance.WellFormedList] at hWFList
        | cons t ts ih =>
          intro hs hWFList hEval targetChild hTarget
          cases hs with
          | nil =>
            exact absurd hTarget (by simp)
          | cons headChild tailChildren =>
            simp only [CInstance.WellFormedList] at hWFList
            obtain ⟨hSrc, hWFh, hWFList⟩ := hWFList
            rcases List.mem_cons.mp hTarget with hEq | hTarget
            · subst targetChild
              have hUniversalHead :
                  UniversalPrenexFormula headChild.source := by
                rw [hSrc]
                exact universalPrenexFormula_formulaSubstN
                  C t x hBodyUniversal
              have hDistinctHead :
                  distinctQuantifierBindings headChild.source := by
                rw [hSrc]
                exact distinctQuantifierBindings_of_formulaSubstN
                  C t x hBodyDistinct
              apply cInstance_eval_of_groundSubstitutions
                headChild hWFh hUniversalHead hDistinctHead M s
              intro tail hTail
              rw [hSrc]
              rw [← applyGroundSubstitution_cons_prenexMatrix_all
                C x t tail hxNotBV]
              apply hEval ((x, t) :: tail)
              simp only [shgPrenexGroundSubstitutionsList,
                List.mem_append, List.mem_map]
              exact Or.inl ⟨tail, hTail, rfl⟩
            · apply ih tailChildren hWFList
              · intro entries hEntries
                apply hEval entries
                simp only [shgPrenexGroundSubstitutionsList,
                  List.mem_append]
                exact Or.inr hEntries
              · exact hTarget
      exact hEvalRest tsRest hsRest hWFRest
        (fun entries hEntries =>
          hPaths entries (by
            simp only [shgPrenexGroundSubstitutions,
              List.mem_append]
            exact Or.inr hEntries))
        mappedChild hMappedChild
termination_by formulaQuantCount ci.source
decreasing_by
  all_goals
    simp_all [CInstance.source, formulaSubst_quantCount,
      formulaQuantCount] /- ATTACH-BLOCKER: private declaration -/

private theorem universalPrenex_eval_prenexMatrix {L : Language}
    (B : FormulaN L) (hUniversal : UniversalPrenexFormula B)
    (M : Structure L) (s : Assignment M)
    (hEval : formulaEvalN M B s) :
    formulaEvalN M (prenexMatrix B) s := by
  induction B generalizing s with
  | all x C ih =>
    have hBody :=
      universalPrenexFormula_body_of_all C x hUniversal
    have hSelf : assignUpdate s x (s x) = s := by
      funext y
      unfold assignUpdate
      split <;> simp_all
    have hEvalC := hEval (s x)
    rw [hSelf] at hEvalC
    exact ih hBody s hEvalC
  | ex x C ih =>
    have hImpossible :=
      hUniversal.2
        (QuantifierKind.existential, x)
        (by simp [prenexPrefix])
    cases hImpossible
  | predN _ _ | eq_ _ _ _ | neg _ | conj _ _ | disj _ _ | impl _ _ =>
    exact hEval /- ATTACH-BLOCKER: private declaration -/

private theorem applyGroundSubstitution_eval_of_all_assignments
    {L : Language} (M : Structure L) :
    ∀ (matrix : FormulaN L) (substs : List (Nat × Term L)),
      (∀ p ∈ substs, Term.isClosed p.2) →
      (∀ s : Assignment M, formulaEvalN M matrix s) →
      ∀ s : Assignment M,
        formulaEvalN M
          (applyGroundSubstitution matrix substs) s := by
  intro matrix substs
  induction substs generalizing matrix with
  | nil =>
    intro hClosed hAll s
    exact hAll s
  | cons p rest ih =>
    intro hClosed hAll s
    have hpClosed : Term.isClosed p.2 :=
      hClosed p List.mem_cons_self
    have hRestClosed :
        ∀ q ∈ rest, Term.isClosed q.2 := by
      intro q hq
      exact hClosed q (List.mem_cons_of_mem _ hq)
    have hSubAll :
        ∀ s' : Assignment M,
          formulaEvalN M
            (formulaSubstN matrix p.2 p.1) s' := by
      intro s'
      rw [formulaSubstEval_closed matrix p.2 p.1 hpClosed s']
      exact hAll _
    exact ih (formulaSubstN matrix p.2 p.1)
      hRestClosed hSubAll s /- ATTACH-BLOCKER: private declaration -/

theorem universalPrenex_eval_groundSubstitution
    {L : Language} (B : FormulaN L)
    (hUniversal : UniversalPrenexFormula B)
    (hClosed : FormulaN.isClosed B)
    (M : Structure L) (s : Assignment M)
    (hEval : formulaEvalN M B s)
    (substs : List (Nat × Term L))
    (hSubstsClosed : ∀ p ∈ substs, Term.isClosed p.2) :
    formulaEvalN M
      (applyGroundSubstitution (prenexMatrix B) substs) s := by
  have hEvalAll : ∀ s' : Assignment M, formulaEvalN M B s' := by
    intro s'
    apply (coincidenceLemmaN M B s s' (fun y hy => ?_)).mp hEval
    rw [hClosed] at hy
    exact hy.elim
  have hMatrixAll :
      ∀ s' : Assignment M,
        formulaEvalN M (prenexMatrix B) s' := by
    intro s'
    exact universalPrenex_eval_prenexMatrix
      B hUniversal M s' (hEvalAll s')
  exact applyGroundSubstitution_eval_of_all_assignments
    M (prenexMatrix B) substs hSubstsClosed hMatrixAll s /- ATTACH-BLOCKER: private declaration -/

-- ===================================================================
-- Corollary 7.6.1: shgCorollary_prenex
-- ===================================================================

/-- Corollary after Theorem 7.6.1: If A is a prenex sentence in NNF, A is unsatisfiable iff a finite conjunction of ground substitution instances of the matrix of the Skolem form B of A is unsatisfiable. Follows from Theorem 7.6.1 (part a): when A is prenex, SK(A) is prenex with only universal quantifiers (existentials eliminated), so any c-instance C of B is (by Def 7.6.3 case iii) a finite conjunction of ground substitution instances of the matrix of B. Under the current metadata policy, this work belongs to Theorem 7.6.1 rather than a standalone corollary item. -/
@[blueprint "chap7__theorem_7_6_1" (main := true)]
theorem shgCorollary_prenex {L : Language}
    (spec : SkolemSpec L)
    (A : FormulaN L)
    (hSource : A = spec.source)
    (hConst : Nonempty L.constSymbols)
    (_hPrenex : LCS.Herbrand.PrenexForm.isPrenex A) :
    ¬ satisfiableN A ↔
      ∃ (F : FormulaN spec.language),
        isFiniteGroundConjunctionOfMatrix F (SK spec) ∧
        ¬ satisfiableN F

end LCS.Herbrand.SHGTheorem.Main
end

