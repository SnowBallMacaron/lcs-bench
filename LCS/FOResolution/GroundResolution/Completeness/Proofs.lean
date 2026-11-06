import LCS.FOResolution.GroundResolution.Completeness

section
namespace LCS.FOResolution.GroundResolution
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FOResolution.ClauseForm
open LCS.FirstOrder.SemanticsN
open LCS.Resolution.GCNF
open LCS.Resolution.Method
open LCS.Resolution.Method.Completeness
open LCS.FirstOrder.SemanticsN
open Classical

proof_of ground_resolution_completeness := by
  -- BEGIN PROOF
    classical
    let atoms := groundClauseSetAtoms (hNoEq := hNoEq) S
    by_cases hAtoms : atoms = []
    · let M : Structure L := {
        carrier := Unit
        carrierNonempty := ⟨()⟩
        interpFunc := fun _ _ => ()
        interpConst := fun _ => ()
        interpPred := fun _ _ => False }
      let s : Assignment M := fun _ => ()
      obtain ⟨c, hc, _⟩ := hUnsat M s
      have hcEmpty : c = [] := by
        cases c with
        | nil => rfl
        | cons lit rest =>
          have hMem :
              groundLiteralAtom (hNoEq := hNoEq) lit ∈ groundClauseSetAtoms (hNoEq := hNoEq) S :=
            groundClauseSetAtoms_mem (hNoEq := hNoEq) S hc (List.mem_cons_self)
          rw [show groundClauseSetAtoms (hNoEq := hNoEq) S = atoms from rfl, hAtoms] at hMem
          exact (List.not_mem_nil hMem).elim
      have hEmptyMem : ([] : FOClause L hNoEq) ∈ S := hcEmpty ▸ hc
      refine ⟨.axiom_ [], hGround, hEmptyMem, ?_⟩
      refine ⟨rfl, ?_⟩
      ext x
      constructor
      · intro ⟨lit, hLit, _⟩
        exact (List.not_mem_nil hLit).elim
      · intro h
        exact h.elim
    · have hAtoms' : atoms ≠ [] := hAtoms
      let encode : FOAtom L hNoEq → Nat := finiteAtomEncode (hNoEq := hNoEq) atoms
      let decode : Nat → FOAtom L hNoEq := finiteAtomDecode (hNoEq := hNoEq) atoms hAtoms'
      have hDecode :
          ∀ c ∈ S, ∀ lit ∈ c,
            decode (encode (groundLiteralAtom (hNoEq := hNoEq) lit)) =
              groundLiteralAtom (hNoEq := hNoEq) lit := by
        intro c hc lit hLit
        exact finiteAtomDecode_encode (hNoEq := hNoEq) atoms hAtoms'
          (groundLiteralAtom (hNoEq := hNoEq) lit)
          (groundClauseSetAtoms_mem (hNoEq := hNoEq) S hc hLit)
      have hNoEqAtom :
          ∀ c ∈ S, ∀ lit ∈ c,
            ∀ (hEq : L.hasEquality = true) (t1 t2 : Term L),
              lit.formula hNoEq ≠ FormulaN.eq_ hEq t1 t2 := by
        intro _ _ _ _ hEq _ _
        have : False := by
          rw [hL] at hEq
          exact Bool.noConfusion hEq
        exact this.elim
      let propS := groundClauseSetToProp (hNoEq := hNoEq) encode S
      have hValid : ClauseSequent.isValid propS :=
        fo_ground_unsat_implies_prop_valid (hNoEq := hNoEq) encode S hGround
          hNoEqAtom hUnsat
      have hPropUnsat : ClauseSet.isUnsatisfiable propS := by
        intro ⟨v, hSat⟩
        exact hValid ⟨v, fun C hC => hSat C hC⟩
      obtain ⟨propTree, hPropLeaves, hPropLabel, hPropWF⟩ :=
        resolution_tree_completeness_isWellFormed propS hPropUnsat
      let foTree := propResTreeToFOResTree (hNoEq := hNoEq) encode decode S propTree
      refine ⟨foTree, hGround,
        propResTree_leaves_from (hNoEq := hNoEq) encode decode propTree S hPropLeaves, ?_⟩
      exact propResTree_empty_label_spec (hNoEq := hNoEq) encode decode S hGround hDecode
        propTree hPropLeaves hPropWF hPropLabel

end LCS.FOResolution.GroundResolution

end
