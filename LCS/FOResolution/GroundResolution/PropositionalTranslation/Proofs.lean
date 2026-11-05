import LCS.FOResolution.GroundResolution.PropositionalTranslation

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


helper def vec2_inj_snd' {a b c d : Term exClauseFormLang}
    (h : vec2 a b = vec2 c d) : b = d := by
  have := congrFun h ⟨1, by omega⟩; simp [vec2] at this; exact this

helper def vec2_inj_fst' {a b c d : Term exClauseFormLang}
    (h : vec2 a b = vec2 c d) : a = c := by
  have := congrFun h ⟨0, by omega⟩; simp [vec2] at this; exact this

helper def predP_inj' {t1 t2 t1' t2' : Term exClauseFormLang}
    (h : exPred_P t1 t2 = exPred_P t1' t2') :
    t1 = t1' ∧ t2 = t2' := by
  unfold exPred_P at h; injection h with _ hv
  exact ⟨vec2_inj_fst' hv, vec2_inj_snd' hv⟩

helper theorem exGroundClause_G1_isGround : FOClause.isGround (by rfl) exGroundClause_G1 := by
  ext x
  constructor
  · intro ⟨lit, hLit, hVar⟩
    simp [exGroundClause_G1] at hLit
    subst lit
    simp only [FOLiteral.vars, FOAtomCore.vars, exPred_P] at hVar
    change ∃ i : Fin 2, termVars (vec2 exSkolemConst_a exSkolemConst_a i) x at hVar
    obtain ⟨⟨i, hiLt⟩, hi⟩ := hVar
    have hiCases : i = 0 ∨ i = 1 := by omega
    rcases hiCases with rfl | rfl <;>
      simp [vec2, exSkolemConst_a, termVars] at hi
  · intro h
    exact h.elim

helper theorem exGroundClause_G2_isGround : FOClause.isGround (by rfl) exGroundClause_G2 := by
  ext x
  constructor
  · intro ⟨lit, hLit, hVar⟩
    simp [exGroundClause_G2] at hLit
    rcases hLit with rfl | rfl
    · simp only [FOLiteral.vars, FOAtomCore.vars, exPred_P] at hVar
      change ∃ i : Fin 2,
        termVars (vec2 exSkolemConst_a exGroundTerm_fa i) x at hVar
      obtain ⟨⟨i, hiLt⟩, hi⟩ := hVar
      have hiCases : i = 0 ∨ i = 1 := by omega
      rcases hiCases with rfl | rfl <;>
        simp [vec2, exSkolemConst_a, exGroundTerm_fa, termVars] at hi
    · simp only [FOLiteral.vars, FOAtomCore.vars, exPred_P] at hVar
      change ∃ i : Fin 2,
        termVars (vec2 exSkolemConst_a exSkolemConst_a i) x at hVar
      obtain ⟨⟨i, hiLt⟩, hi⟩ := hVar
      have hiCases : i = 0 ∨ i = 1 := by omega
      rcases hiCases with rfl | rfl <;>
        simp [vec2, exSkolemConst_a, termVars] at hi
  · intro h
    exact h.elim

helper theorem exGroundClause_G3_isGround : FOClause.isGround (by rfl) exGroundClause_G3 := by
  ext x
  constructor
  · intro ⟨lit, hLit, hVar⟩
    simp [exGroundClause_G3] at hLit
    rcases hLit with rfl | rfl
    · simp only [FOLiteral.vars, FOAtomCore.vars, exPred_P] at hVar
      change ∃ i : Fin 2,
        termVars (vec2 exGroundTerm_fa exSkolemConst_a i) x at hVar
      obtain ⟨⟨i, hiLt⟩, hi⟩ := hVar
      have hiCases : i = 0 ∨ i = 1 := by omega
      rcases hiCases with rfl | rfl <;>
        simp [vec2, exSkolemConst_a, exGroundTerm_fa, termVars] at hi
    · simp only [FOLiteral.vars, FOAtomCore.vars, exPred_P] at hVar
      change ∃ i : Fin 2,
        termVars (vec2 exSkolemConst_a exSkolemConst_a i) x at hVar
      obtain ⟨⟨i, hiLt⟩, hi⟩ := hVar
      have hiCases : i = 0 ∨ i = 1 := by omega
      rcases hiCases with rfl | rfl <;>
        simp [vec2, exSkolemConst_a, termVars] at hi
  · intro h
    exact h.elim

helper theorem exGroundClause_G4_isGround : FOClause.isGround (by rfl) exGroundClause_G4 := by
  ext x
  constructor
  · intro ⟨lit, hLit, hVar⟩
    simp [exGroundClause_G4] at hLit
    rcases hLit with rfl | rfl
    · simp only [FOLiteral.vars, FOAtomCore.vars, exPred_P] at hVar
      change ∃ i : Fin 2,
        termVars (vec2 exGroundTerm_fa exSkolemConst_a i) x at hVar
      obtain ⟨⟨i, hiLt⟩, hi⟩ := hVar
      have hiCases : i = 0 ∨ i = 1 := by omega
      rcases hiCases with rfl | rfl <;>
        simp [vec2, exSkolemConst_a, exGroundTerm_fa, termVars] at hi
    · simp only [FOLiteral.vars, FOAtomCore.vars, exPred_P] at hVar
      change ∃ i : Fin 2,
        termVars (vec2 exSkolemConst_a exGroundTerm_fa i) x at hVar
      obtain ⟨⟨i, hiLt⟩, hi⟩ := hVar
      have hiCases : i = 0 ∨ i = 1 := by omega
      rcases hiCases with rfl | rfl <;>
        simp [vec2, exSkolemConst_a, exGroundTerm_fa, termVars] at hi
  · intro h
    exact h.elim

helper theorem step1_label' :
    FOResolutionTree.labelSpec (hNoEq := by rfl) exGroundResolution_step1
      [FOLiteralCore.pos (exPred_P exSkolemConst_a exGroundTerm_fa)] := by
-- BEGIN PROOF
  simp only [exGroundResolution_step1, FOResolutionTree.labelSpec]
  refine ⟨exGroundClause_G2, exGroundClause_G1,
    ⟨rfl, exGroundClause_G2_isGround⟩,
    ⟨rfl, exGroundClause_G1_isGround⟩, ?_, ?_, ?_, ?_⟩
  · unfold exGroundClause_G2
    simp
  · unfold exGroundClause_G1
    simp [FOLiteral.conjugate, FOLiteralCore.conjugate]
  · exact FOClause.isGround_of_subset (hNoEq := by rfl) exGroundClause_G2_isGround
      (fun lit hLit => by
        simp at hLit
        subst lit
        unfold exGroundClause_G2
        simp)
  intro lit; constructor
  · intro hmem; simp [List.mem_cons] at hmem; subst hmem
    left; exact ⟨by unfold exGroundClause_G2; simp,
      fun heq => nomatch (predP_inj' (FOLiteralCore.pos.inj heq)).2⟩
  · intro h; rcases h with ⟨hmem, hne⟩ | ⟨hmem, hne⟩
    · unfold exGroundClause_G2 at hmem; simp [List.mem_cons] at hmem
      rcases hmem with h1 | h2
      · simp [h1]
      · exact absurd h2 hne
    · unfold exGroundClause_G1 at hmem; simp [List.mem_cons] at hmem
      exfalso; apply hne; simp [FOLiteral.conjugate, FOLiteralCore.conjugate, hmem]

helper theorem step2_label' :
    FOResolutionTree.labelSpec (hNoEq := by rfl) exGroundResolution_step2
      [FOLiteralCore.pos (exPred_P exGroundTerm_fa exSkolemConst_a)] := by
-- BEGIN PROOF
  simp only [exGroundResolution_step2, FOResolutionTree.labelSpec]
  refine ⟨exGroundClause_G3, exGroundClause_G1,
    ⟨rfl, exGroundClause_G3_isGround⟩,
    ⟨rfl, exGroundClause_G1_isGround⟩, ?_, ?_, ?_, ?_⟩
  · unfold exGroundClause_G3
    simp
  · unfold exGroundClause_G1
    simp [FOLiteral.conjugate, FOLiteralCore.conjugate]
  · exact FOClause.isGround_of_subset (hNoEq := by rfl) exGroundClause_G3_isGround
      (fun lit hLit => by
        simp at hLit
        subst lit
        unfold exGroundClause_G3
        simp)
  intro lit; constructor
  · intro hmem; simp [List.mem_cons] at hmem; subst hmem
    left; exact ⟨by unfold exGroundClause_G3; simp,
      fun heq => nomatch (predP_inj' (FOLiteralCore.pos.inj heq)).1⟩
  · intro h; rcases h with ⟨hmem, hne⟩ | ⟨hmem, hne⟩
    · unfold exGroundClause_G3 at hmem; simp [List.mem_cons] at hmem
      rcases hmem with h1 | h2
      · simp [h1]
      · exact absurd h2 hne
    · unfold exGroundClause_G1 at hmem; simp [List.mem_cons] at hmem
      exfalso; apply hne; simp [FOLiteral.conjugate, FOLiteralCore.conjugate, hmem]

helper theorem step3_label' :
    FOResolutionTree.labelSpec (hNoEq := by rfl) exGroundResolution_step3
      [FOLiteralCore.neg (exPred_P exSkolemConst_a exGroundTerm_fa)] := by
-- BEGIN PROOF
  simp only [exGroundResolution_step3, FOResolutionTree.labelSpec]
  refine ⟨[FOLiteralCore.pos (exPred_P exGroundTerm_fa exSkolemConst_a)],
          exGroundClause_G4, step2_label',
          ⟨rfl, exGroundClause_G4_isGround⟩, ?_, ?_, ?_, ?_⟩
  · simp
  · unfold exGroundClause_G4
    simp [FOLiteral.conjugate, FOLiteralCore.conjugate]
  · exact FOClause.isGround_of_subset (hNoEq := by rfl) exGroundClause_G4_isGround
      (fun lit hLit => by
        simp at hLit
        subst lit
        unfold exGroundClause_G4
        simp)
  intro lit; constructor
  · intro hmem; simp [List.mem_cons] at hmem; subst hmem
    right; refine ⟨by unfold exGroundClause_G4; simp, ?_⟩
    simp [FOLiteral.conjugate, FOLiteralCore.conjugate]
    intro heq; exact nomatch (predP_inj' heq).1.symm
  · intro h; rcases h with ⟨hmem, hne⟩ | ⟨hmem, hne⟩
    · simp [List.mem_cons] at hmem; exact absurd hmem hne
    · unfold exGroundClause_G4 at hmem; simp [List.mem_cons] at hmem
      rcases hmem with h1 | h2
      · exfalso; apply hne; simp [FOLiteral.conjugate, FOLiteralCore.conjugate, h1]
      · simp [h2]

proof_of exGroundResolution_refutation_label_empty := by
  -- BEGIN PROOF
    unfold exGroundResolution_refutation exGroundResolution_step4
    simp only [FOResolutionTree.labelSpec]
    refine ⟨[FOLiteralCore.pos (exPred_P exSkolemConst_a exGroundTerm_fa)],
            [FOLiteralCore.neg (exPred_P exSkolemConst_a exGroundTerm_fa)],
            step1_label', step3_label', ?_, ?_, ?_, ?_⟩
    · simp
    · simp [FOLiteral.conjugate, FOLiteralCore.conjugate]
    · ext x
      constructor
      · intro ⟨lit, hLit, _⟩
        exact (List.not_mem_nil hLit).elim
      · intro h
        exact h.elim
    intro lit; constructor
    · intro hmem; simp at hmem
    · intro h; rcases h with ⟨hmem, hne⟩ | ⟨hmem, hne⟩
      · simp [List.mem_cons] at hmem; exact absurd hmem hne
      · simp [List.mem_cons] at hmem; exact absurd hmem hne


end LCS.FOResolution.GroundResolution

end
