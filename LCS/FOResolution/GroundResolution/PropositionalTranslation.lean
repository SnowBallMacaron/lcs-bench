import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.Resolution.Method.Completeness
import LCS.Resolution.Method.Unfold
import LCS.FOResolution.GroundResolution.GroundClauses
import Attach
import LCS.FOResolution.GroundResolution.PropositionalTranslation.ProofsStamp

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
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
theorem fo_ground_unsat_implies_prop_valid {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat)
    (S : List (FOClause L hNoEq))
    (hGround : ∀ c ∈ S, FOClause.isGround hNoEq c)
    (hNoEqAtom : ∀ c ∈ S, ∀ lit ∈ c,
      ∀ (hL : L.hasEquality = true) (t1 t2 : Term L),
        lit.formula hNoEq ≠ FormulaN.eq_ hL t1 t2)
    (hUnsat : GroundClauseSet.isUnsatisfiable (hNoEq := hNoEq) S) :
    ClauseSequent.isValid (groundClauseSetToProp (hNoEq := hNoEq) encode S) := by
-- BEGIN PROOF
  -- Assume for contradiction that some valuation v satisfies all
  -- translated clauses.
  intro ⟨v, hSat⟩
  -- From v, define a truth assignment on first-order atoms:
  -- an atomic formula B is true iff v(encode B) = true.
  let truthVal : FOAtom L hNoEq → Prop := fun B => v (encode B) = true
  -- Build the Herbrand structure with this truth assignment.
  let M := herbrandStructure (hNoEq := hNoEq) truthVal
  let s : Assignment M := fun n => Term.var n
  -- By hUnsat, some clause c in S is not satisfied by M, s.
  obtain ⟨c, hc_mem, hc_unsat⟩ := hUnsat M s
  -- But v satisfies the propositional translation of c.
  have hc_prop_sat : ClauseSet.satisfies v (groundClauseSetToProp (hNoEq := hNoEq) encode S) := by
    exact fun C hC => hSat C hC
  have hc_translated_sat :
      Clause.satisfies v (groundClauseToProp (hNoEq := hNoEq) encode c) := by
    apply hc_prop_sat
    simp only [groundClauseSetToProp, Finset.mem_ofList]
    exact List.mem_map.mpr ⟨c, hc_mem, rfl⟩
  -- From the propositional satisfaction, extract a literal that is satisfied.
  obtain ⟨pL, hpL_mem, hpL_sat⟩ := hc_translated_sat
  simp only [groundClauseToProp, Finset.mem_ofList] at hpL_mem
  obtain ⟨folit, hfolit_mem, hfolit_eq⟩ := List.mem_map.mp hpL_mem
  -- This FO literal should be satisfied by M, s.
  -- This contradicts hc_unsat.
  apply hc_unsat
  refine ⟨folit, hfolit_mem, ?_⟩
  -- The ground literal folit is pos B or neg B. The propositional
  -- literal is satisfied by v, meaning v(encode B) has the right value.
  -- In the Herbrand structure, truthVal B = (v(encode B) = true).
  -- For ground atomic formulas, herbrand_predN_eval connects these.
  -- We handle each literal polarity and use the Herbrand model
  -- interpretation, which directly stores truthVal for atomic predicates.
  rw [← hfolit_eq] at hpL_sat
  -- Helper: extract groundness of predN args from clause-level groundness
  have arg_ground : ∀ (lit : FOLiteral L hNoEq) (P : L.predSymbols)
      (args : Fin (L.predArity P) → Term L),
      lit ∈ c → lit.formula hNoEq = FormulaN.predN P args →
      ∀ i, termVars (args i) = Set.empty := by
    intro lit P args hlit_mem hlit_form i
    have hc_ground := hGround c hc_mem
    unfold FOClause.isGround at hc_ground
    funext m; apply propext; constructor
    · intro hm
      have : FOClause.vars hNoEq c m := by
        refine ⟨lit, hlit_mem, ?_⟩
        show FOLiteral.vars hNoEq lit m
        change FOLiteralCore.vars lit m
        dsimp only [FOLiteral.formula] at hlit_form
        rw [FOLiteralCore.vars_eq_formulaVars, hlit_form]
        show formulaVars (FormulaN.predN P args) m
        exact ⟨i, hm⟩
      dsimp only [FOClause.vars] at this
      rw [hc_ground] at this; exact this
    · exact False.elim
  -- Helper: connect Herbrand formulaEvalN with truthVal for atomic ground lits
  have herbrand_atomic : ∀ (P : L.predSymbols)
      (args : Fin (L.predArity P) → Term L),
      (∀ i, termVars (args i) = Set.empty) →
      (formulaEvalN M (FormulaN.predN P args) s ↔
        truthVal (FOAtomCore.predN P args)) := by
    intro P args hArgsGround
    have hargs_eq : (fun i => termEval M s (args i)) = args := by
      funext i; exact herbrand_termEval_ground (hNoEq := hNoEq) truthVal s (args i) (hArgsGround i)
    simp only [formulaEvalN]
    show M.interpPred P (fun i => termEval M s (args i)) ↔
      truthVal (FOAtomCore.predN P args)
    rw [hargs_eq]
    exact Iff.rfl
  cases folit with
  | pos B =>
    simp only [FOLiteral.isSatisfied]
    simp only [groundLiteralToProp, Literal.satisfiedBy] at hpL_sat
    -- hpL_sat : v (encode B) = true, need: formulaEvalN M B.toFormula s
    -- Rule out eq_ via hNoEqAtom
    have hNotEq : ∀ (hL : L.hasEquality = true) (t1 t2 : Term L),
        B.toFormula ≠ FormulaN.eq_ hL t1 t2 := by
      intro hL t1 t2
      exact hNoEqAtom c hc_mem (.pos B) hfolit_mem hL t1 t2
    match B, hNotEq with
    | .predN P args, _ =>
      have hArgsGround := arg_ground (.pos (.predN P args)) P args hfolit_mem rfl
      exact (herbrand_atomic P args hArgsGround).mpr hpL_sat
    | .eq_ hL t1 t2, hNE => exact absurd rfl (hNE hL t1 t2)
  | neg B =>
    simp only [FOLiteral.isSatisfied]
    simp only [groundLiteralToProp, Literal.satisfiedBy] at hpL_sat
    -- hpL_sat : v (encode B) = false, need: ¬ formulaEvalN M B.toFormula s
    -- Rule out eq_ via hNoEqAtom
    have hNotEq : ∀ (hL : L.hasEquality = true) (t1 t2 : Term L),
        B.toFormula ≠ FormulaN.eq_ hL t1 t2 := by
      intro hL t1 t2
      exact hNoEqAtom c hc_mem (.neg B) hfolit_mem hL t1 t2
    match B, hNotEq with
    | .predN P args, _ =>
      have hArgsGround := arg_ground (.neg (.predN P args)) P args hfolit_mem rfl
      intro heval
      have := (herbrand_atomic P args hArgsGround).mp heval
      -- this : truthVal (predN P args) i.e. v (encode (predN P args)) = true
      -- hpL_sat : v (encode (predN P args)) = false
      exact absurd this (by simp only [truthVal]; rw [hpL_sat]; decide)
    | .eq_ hL t1 t2, hNE => exact absurd rfl (hNE hL t1 t2)

-- ===================================================================
-- FO resolution tree to propositional resolution tree translation
-- ===================================================================
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- Translate an FO resolution tree to a propositional resolution tree
    via the encoding. Each leaf axiom clause is translated, and each
    resolution pivot is translated. -/
def foResTreeToResTree {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat) :
    FOResolutionTree L hNoEq → ResolutionTree
  | .axiom_ C => ResolutionTree.axiom_ (groundClauseToProp (hNoEq := hNoEq) encode C)
  | .resolve T1 T2 pivot =>
    ResolutionTree.resolve
      (foResTreeToResTree (hNoEq := hNoEq) encode T1)
      (foResTreeToResTree (hNoEq := hNoEq) encode T2)
      (groundLiteralToProp (hNoEq := hNoEq) encode pivot)

-- ===================================================================
-- Translation preserves leaves-from
-- ===================================================================
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- If the leaves of an FO resolution tree come from the list S,
    then the leaves of the translated propositional tree come from
    the translated clause sequent. -/
theorem foResTree_leavesFrom {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat)
    (T : FOResolutionTree L hNoEq)
    (S : List (FOClause L hNoEq))
    (hLeaves : T.leavesFrom (hNoEq := hNoEq) (fun c => c ∈ S)) :
    (foResTreeToResTree (hNoEq := hNoEq) encode T).leavesFrom
      (groundClauseSetToProp (hNoEq := hNoEq) encode S) := by
-- BEGIN PROOF
  induction T with
  | axiom_ C =>
    simp only [FOResolutionTree.leavesFrom] at hLeaves
    simp only [foResTreeToResTree, ResolutionTree.leavesFrom,
               groundClauseSetToProp, Finset.mem_ofList]
    exact List.mem_map.mpr ⟨C, hLeaves, rfl⟩
  | resolve T1 T2 pivot ih1 ih2 =>
    simp only [FOResolutionTree.leavesFrom] at hLeaves
    simp only [foResTreeToResTree, ResolutionTree.leavesFrom]
    exact ⟨ih1 hLeaves.1, ih2 hLeaves.2⟩


-- ===================================================================
-- Propositional resolution tree to FO resolution tree: Classical approach
-- ===================================================================
-- Instead of decoding prop clauses (which would require dealing with
-- Finset internal ordering), we use Classical.choice to select the
-- original FO clause from S for each prop tree leaf.
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- Decode a propositional literal to a first-order literal. -/
def decodePropLiteral {L : Language} (hNoEq : L.withoutEquality)
    (decode : Nat → FOAtom L hNoEq) : Literal → FOLiteral L hNoEq
  | .pos n => FOLiteralCore.pos (decode n)
  | .neg n => FOLiteralCore.neg (decode n)
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- A source-local decoder inverts literal encoding whenever the atom is in
    the finite source list. -/
theorem decode_groundLiteralToProp {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat) (decode : Nat → FOAtom L hNoEq)
    (lit : FOLiteral L hNoEq)
    (hDecode : decode (encode (groundLiteralAtom (hNoEq := hNoEq) lit)) =
      groundLiteralAtom (hNoEq := hNoEq) lit) :
    decodePropLiteral (hNoEq := hNoEq) decode (groundLiteralToProp (hNoEq := hNoEq) encode lit) = lit := by
  cases lit <;>
    simp only [groundLiteralAtom] at hDecode <;>
    simp [decodePropLiteral, groundLiteralToProp, hDecode]
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- Build an FO resolution tree from a propositional resolution tree,
    using Classical.choice to select the original FO clause from S for
    each leaf. For resolve nodes, the pivot is decoded via decode. -/
noncomputable def propResTreeToFOResTree {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat)
    (decode : Nat → FOAtom L hNoEq)
    (S : List (FOClause L hNoEq)) :
    ResolutionTree → FOResolutionTree L hNoEq
  | .axiom_ C =>
    let foClause := if h : ∃ c ∈ S, groundClauseToProp (hNoEq := hNoEq) encode c = C
      then Classical.choose h
      else []
    .axiom_ foClause
  | .resolve T1 T2 pivot =>
    .resolve (propResTreeToFOResTree (hNoEq := hNoEq) encode decode S T1)
             (propResTreeToFOResTree (hNoEq := hNoEq) encode decode S T2)
             (decodePropLiteral (hNoEq := hNoEq) decode pivot)
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- Encoding preserves literal conjugation under decoding. -/
theorem decodePropLiteral_conjugate {L : Language} (hNoEq : L.withoutEquality)
    (decode : Nat → FOAtom L hNoEq) (lit : Literal) :
    decodePropLiteral (hNoEq := hNoEq) decode (Literal.conjugate lit) =
    FOLiteral.conjugate hNoEq (decodePropLiteral (hNoEq := hNoEq) decode lit) := by
-- BEGIN PROOF
  cases lit with
  | pos n => rfl
  | neg n => rfl
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- Encoding a ground FO literal and then decoding gives back the original. -/
theorem groundLiteralToProp_decodePropLiteral {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat) (decode : Nat → FOAtom L hNoEq)
    (hdec : ∀ B, decode (encode B) = B)
    (lit : FOLiteral L hNoEq) :
    decodePropLiteral (hNoEq := hNoEq) decode (groundLiteralToProp (hNoEq := hNoEq) encode lit) = lit := by
-- BEGIN PROOF
  cases lit with
  | pos B => simp [groundLiteralToProp, decodePropLiteral, hdec]
  | neg B => simp [groundLiteralToProp, decodePropLiteral, hdec]
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- If the prop tree leaves come from the encoded FO clause set,
    the FO translation's leaves come from S. -/
theorem propResTree_leaves_from {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat)
    (decode : Nat → FOAtom L hNoEq)
    (T : ResolutionTree) (S : List (FOClause L hNoEq))
    (hLeaves : T.leavesFrom (groundClauseSetToProp (hNoEq := hNoEq) encode S)) :
    (propResTreeToFOResTree (hNoEq := hNoEq) encode decode S T).leavesFrom (hNoEq := hNoEq) (fun c => c ∈ S) := by
-- BEGIN PROOF
  induction T with
  | axiom_ C =>
    simp only [propResTreeToFOResTree, FOResolutionTree.leavesFrom]
    simp only [ResolutionTree.leavesFrom, groundClauseSetToProp,
               Finset.mem_ofList] at hLeaves
    obtain ⟨c, hc_mem, hc_eq⟩ := List.mem_map.mp hLeaves
    have hex : ∃ c ∈ S, groundClauseToProp (hNoEq := hNoEq) encode c = C := ⟨c, hc_mem, hc_eq⟩
    simp only [hex, dite_true]
    exact (Classical.choose_spec hex).1
  | resolve T1 T2 pivot ih1 ih2 =>
    simp only [propResTreeToFOResTree, FOResolutionTree.leavesFrom]
    simp only [ResolutionTree.leavesFrom] at hLeaves
    exact ⟨ih1 hLeaves.1, ih2 hLeaves.2⟩

-- ===================================================================
-- Label specification: the FO tree tracks the prop tree's label
-- ===================================================================
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- A structurally valid propositional resolution tree translates to a
    structurally valid ground first-order tree.  Besides the label
    certificate, the result records source provenance and the exact
    correspondence between propositional and first-order label membership. -/
theorem propResTree_labelSpec_general {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat)
    (decode : Nat → FOAtom L hNoEq)
    (S : List (FOClause L hNoEq))
    (hGround : ∀ c ∈ S, FOClause.isGround hNoEq c)
    (hdec : ∀ c ∈ S, ∀ lit ∈ c,
      decode (encode (groundLiteralAtom (hNoEq := hNoEq) lit)) = groundLiteralAtom (hNoEq := hNoEq) lit)
    (T : ResolutionTree)
    (hLeaves : T.leavesFrom (groundClauseSetToProp (hNoEq := hNoEq) encode S))
    (hWF : T.IsWellFormed) :
    ∃ (C : FOClause L hNoEq),
      FOResolutionTree.labelSpec (hNoEq := hNoEq) (propResTreeToFOResTree (hNoEq := hNoEq) encode decode S T) C ∧
      (∀ folit, folit ∈ C → ∃ c ∈ S, folit ∈ c) ∧
      (∀ plit, plit ∈ T.label ↔
        ∃ folit ∈ C, groundLiteralToProp (hNoEq := hNoEq) encode folit = plit) := by
-- BEGIN PROOF
  induction T with
  | axiom_ propC =>
    simp only [propResTreeToFOResTree, FOResolutionTree.labelSpec, ResolutionTree.label]
    simp only [ResolutionTree.leavesFrom, groundClauseSetToProp,
               Finset.mem_ofList] at hLeaves
    obtain ⟨c, hc_mem, hc_eq⟩ := List.mem_map.mp hLeaves
    have hex : ∃ c ∈ S, groundClauseToProp (hNoEq := hNoEq) encode c = propC := ⟨c, hc_mem, hc_eq⟩
    simp only [hex, dite_true]
    have hspec := Classical.choose_spec hex
    refine ⟨Classical.choose hex,
      ⟨rfl, hGround (Classical.choose hex) hspec.1⟩, ?_, ?_⟩
    · intro folit hfolit
      exact ⟨Classical.choose hex, hspec.1, hfolit⟩
    · intro plit
      constructor
      · intro hProp
        have h :
            plit ∈ groundClauseToProp (hNoEq := hNoEq) encode (Classical.choose hex) := by
          rw [hspec.2]
          exact hProp
        simp only [groundClauseToProp, Finset.mem_ofList] at h
        obtain ⟨folit, hfolit, hEq⟩ := List.mem_map.mp h
        exact ⟨folit, hfolit, hEq⟩
      · rintro ⟨folit, hfolit, rfl⟩
        have h :
            groundLiteralToProp (hNoEq := hNoEq) encode folit ∈
              groundClauseToProp (hNoEq := hNoEq) encode (Classical.choose hex) := by
          simp only [groundClauseToProp, Finset.mem_ofList]
          exact List.mem_map.mpr ⟨folit, hfolit, rfl⟩
        rw [hspec.2] at h
        exact h
  | resolve T1 T2 pivot ih1 ih2 =>
    simp only [ResolutionTree.leavesFrom] at hLeaves
    simp only [ResolutionTree.IsWellFormed] at hWF
    obtain ⟨hWF1, hWF2, hPivot, hConj⟩ := hWF
    obtain ⟨C1, hC1spec, hC1origin, hC1enc⟩ :=
      ih1 hLeaves.1 hWF1
    obtain ⟨C2, hC2spec, hC2origin, hC2enc⟩ :=
      ih2 hLeaves.2 hWF2
    simp only [propResTreeToFOResTree, FOResolutionTree.labelSpec]
    classical
    let foPivot := decodePropLiteral (hNoEq := hNoEq) decode pivot
    let foLabel := C1.filter (· ≠ foPivot) ++ C2.filter (· ≠ FOLiteral.conjugate hNoEq foPivot)
    obtain ⟨leftPivot, hLeftPivotMem, hLeftPivotEnc⟩ :=
      (hC1enc pivot).mp hPivot
    obtain ⟨leftSource, hLeftSource, hLeftPivotSource⟩ :=
      hC1origin leftPivot hLeftPivotMem
    have hLeftDecode :
        decode (encode (groundLiteralAtom (hNoEq := hNoEq) leftPivot)) =
          groundLiteralAtom (hNoEq := hNoEq) leftPivot :=
      hdec leftSource hLeftSource leftPivot hLeftPivotSource
    have hLeftPivotEq : leftPivot = foPivot := by
      have hDecoded :=
        decode_groundLiteralToProp (hNoEq := hNoEq) encode decode leftPivot hLeftDecode
      rw [hLeftPivotEnc] at hDecoded
      exact hDecoded.symm
    have hFoPivotMem : foPivot ∈ C1 := hLeftPivotEq ▸ hLeftPivotMem
    have hEncodeFoPivot :
        groundLiteralToProp (hNoEq := hNoEq) encode foPivot = pivot := by
      rw [← hLeftPivotEq]
      exact hLeftPivotEnc
    obtain ⟨rightPivot, hRightPivotMem, hRightPivotEnc⟩ :=
      (hC2enc (Literal.conjugate pivot)).mp hConj
    obtain ⟨rightSource, hRightSource, hRightPivotSource⟩ :=
      hC2origin rightPivot hRightPivotMem
    have hRightDecode :
        decode (encode (groundLiteralAtom (hNoEq := hNoEq) rightPivot)) =
          groundLiteralAtom (hNoEq := hNoEq) rightPivot :=
      hdec rightSource hRightSource rightPivot hRightPivotSource
    have hRightPivotEq :
        rightPivot = FOLiteral.conjugate hNoEq foPivot := by
      have hDecoded :=
        decode_groundLiteralToProp (hNoEq := hNoEq) encode decode rightPivot hRightDecode
      rw [hRightPivotEnc] at hDecoded
      rw [decodePropLiteral_conjugate (hNoEq := hNoEq)] at hDecoded
      exact hDecoded.symm
    have hFoConjMem : FOLiteral.conjugate hNoEq foPivot ∈ C2 :=
      hRightPivotEq ▸ hRightPivotMem
    have hEncodeFoConj :
        groundLiteralToProp (hNoEq := hNoEq) encode (FOLiteral.conjugate hNoEq foPivot) =
          Literal.conjugate pivot := by
      rw [← groundLiteralToProp_conjugate (hNoEq := hNoEq), hEncodeFoPivot]
    have hC1Ground := FOResolutionTree.labelSpec_isGround (hNoEq := hNoEq) hC1spec
    have hC2Ground := FOResolutionTree.labelSpec_isGround (hNoEq := hNoEq) hC2spec
    have hLeftFilterGround :
        FOClause.isGround hNoEq (C1.filter (· ≠ foPivot)) :=
      FOClause.isGround_of_subset (hNoEq := hNoEq) hC1Ground
        (fun lit hLit => (List.mem_filter.mp hLit).1)
    have hRightFilterGround :
        FOClause.isGround hNoEq
          (C2.filter (· ≠ FOLiteral.conjugate hNoEq foPivot)) :=
      FOClause.isGround_of_subset (hNoEq := hNoEq) hC2Ground
        (fun lit hLit => (List.mem_filter.mp hLit).1)
    have hFoLabelGround : FOClause.isGround hNoEq foLabel :=
      FOClause.isGround_append (hNoEq := hNoEq) hLeftFilterGround hRightFilterGround
    refine ⟨foLabel,
      ⟨C1, C2, hC1spec, hC2spec, hFoPivotMem, hFoConjMem,
        hFoLabelGround, ?_⟩, ?_, ?_⟩
    · intro lit
      constructor
      · intro hmem
        simp only [foLabel, List.mem_append, List.mem_filter, decide_eq_true_eq] at hmem
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
      · intro h
        simp only [foLabel, List.mem_append, List.mem_filter, decide_eq_true_eq]
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
    · intro folit hfolit
      simp only [foLabel, List.mem_append, List.mem_filter,
        decide_eq_true_eq] at hfolit
      rcases hfolit with ⟨hMem, _⟩ | ⟨hMem, _⟩
      · exact hC1origin folit hMem
      · exact hC2origin folit hMem
    · intro plit
      change
        plit ∈ Finset.union (Finset.erase T1.label pivot)
            (Finset.erase T2.label (Literal.conjugate pivot)) ↔ _
      rw [Finset.mem_union]
      constructor
      · intro hmem
        rcases hmem with hmem | hmem
        · obtain ⟨hChildMem, hNe⟩ :=
            (Finset.mem_erase pivot plit T1.label).mp hmem
          obtain ⟨folit, hFolit, hEnc⟩ :=
            (hC1enc plit).mp hChildMem
          have hFolitNe : folit ≠ foPivot := by
            intro hEq
            apply hNe
            rw [← hEnc, hEq, hEncodeFoPivot]
          exact ⟨folit, by
            simp only [foLabel, List.mem_append, List.mem_filter,
              decide_eq_true_eq]
            exact Or.inl ⟨hFolit, hFolitNe⟩, hEnc⟩
        · obtain ⟨hChildMem, hNe⟩ :=
            (Finset.mem_erase
              (Literal.conjugate pivot) plit T2.label).mp hmem
          obtain ⟨folit, hFolit, hEnc⟩ :=
            (hC2enc plit).mp hChildMem
          have hFolitNe :
              folit ≠ FOLiteral.conjugate hNoEq foPivot := by
            intro hEq
            apply hNe
            rw [← hEnc, hEq, hEncodeFoConj]
          exact ⟨folit, by
            simp only [foLabel, List.mem_append, List.mem_filter,
              decide_eq_true_eq]
            exact Or.inr ⟨hFolit, hFolitNe⟩, hEnc⟩
      · rintro ⟨folit, hFolit, rfl⟩
        simp only [foLabel, List.mem_append, List.mem_filter,
          decide_eq_true_eq] at hFolit
        rcases hFolit with ⟨hChildMem, hNe⟩ | ⟨hChildMem, hNe⟩
        · apply Or.inl
          apply (Finset.mem_erase pivot
            (groundLiteralToProp (hNoEq := hNoEq) encode folit) T1.label).mpr
          refine ⟨(hC1enc _).mpr ⟨folit, hChildMem, rfl⟩, ?_⟩
          intro hEncEq
          obtain ⟨source, hSource, hFolitSource⟩ :=
            hC1origin folit hChildMem
          have hDecoded := decode_groundLiteralToProp (hNoEq := hNoEq) encode decode folit
            (hdec source hSource folit hFolitSource)
          rw [hEncEq] at hDecoded
          exact hNe hDecoded.symm
        · apply Or.inr
          apply (Finset.mem_erase (Literal.conjugate pivot)
            (groundLiteralToProp (hNoEq := hNoEq) encode folit) T2.label).mpr
          refine ⟨(hC2enc _).mpr ⟨folit, hChildMem, rfl⟩, ?_⟩
          intro hEncEq
          obtain ⟨source, hSource, hFolitSource⟩ :=
            hC2origin folit hChildMem
          have hDecoded := decode_groundLiteralToProp (hNoEq := hNoEq) encode decode folit
            (hdec source hSource folit hFolitSource)
          rw [hEncEq, decodePropLiteral_conjugate (hNoEq := hNoEq)] at hDecoded
          exact hNe hDecoded.symm
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- If the prop tree has empty label, the FO tree has labelSpec []. -/
theorem propResTree_empty_label_spec {L : Language} (hNoEq : L.withoutEquality)
    (encode : FOAtom L hNoEq → Nat)
    (decode : Nat → FOAtom L hNoEq)
    (S : List (FOClause L hNoEq))
    (hGround : ∀ c ∈ S, FOClause.isGround hNoEq c)
    (hdec : ∀ c ∈ S, ∀ lit ∈ c,
      decode (encode (groundLiteralAtom (hNoEq := hNoEq) lit)) = groundLiteralAtom (hNoEq := hNoEq) lit)
    (T : ResolutionTree)
    (hLeaves : T.leavesFrom (groundClauseSetToProp (hNoEq := hNoEq) encode S))
    (hWF : T.IsWellFormed)
    (hLabel : T.label = LCS.Resolution.GCNF.Clause.empty) :
    FOResolutionTree.labelSpec (hNoEq := hNoEq) (propResTreeToFOResTree (hNoEq := hNoEq) encode decode S T) [] := by
-- BEGIN PROOF
  obtain ⟨C, hCspec, _, hCenc⟩ :=
    propResTree_labelSpec_general (hNoEq := hNoEq) encode decode S hGround hdec T hLeaves hWF
  suffices hnil : C = [] by rw [hnil] at hCspec; exact hCspec
  cases C with
  | nil => rfl
  | cons x xs =>
    exfalso
    have hmem := (hCenc (groundLiteralToProp (hNoEq := hNoEq) encode x)).mpr
      ⟨x, List.mem_cons.mpr (Or.inl rfl), rfl⟩
    -- hmem : groundLiteralToProp encode x ∈ T.label
    -- T.label = Clause.empty, so T.label has no elements
    have : T.label = Finset.empty := by
      rw [hLabel]; rfl
    rw [this] at hmem
    exact (Finset.mem_empty _).mp hmem
-- ATTACH-BLOCKER: size baseline: retain the resolution translation helper group
/-- Propositional completeness with the structural certificate needed to
    translate a refutation into a ground first-order resolution tree. -/
theorem resolution_tree_completeness_isWellFormed (S : ClauseSequent)
    (hUnsat : ClauseSet.isUnsatisfiable S) :
    ∃ T : ResolutionTree,
      T.leavesFrom S ∧ T.label = LCS.Resolution.GCNF.Clause.empty ∧ T.IsWellFormed := by
  classical
  by_cases hEmpty : LCS.Resolution.GCNF.Clause.empty ∈ S
  · exact ⟨.axiom_ LCS.Resolution.GCNF.Clause.empty, hEmpty, rfl, True.intro⟩
  · have hValid : ClauseSequent.isValid S := by
      intro ⟨v, hSat⟩
      exact hUnsat ⟨v, hSat⟩
    have hNe : ∀ C ∈ S, C ≠ LCS.Resolution.GCNF.Clause.empty :=
      fun C hC he => hEmpty (he ▸ hC)
    obtain ⟨T⟩ := (gcnf_completeness S hValid hNe).1
    let g := gcnfProofToResolution T
    have hRef := (gcnfProofToResolution_spec T).1
    refine ⟨g.unfold hRef.1,
      (g.unfold_leavesFrom hRef.1 S).mpr hRef.2.1, ?_,
      g.unfold_isWellFormed hRef.1⟩
    exact Option.some.inj ((g.unfold_rootLabel hRef.1).symm.trans hRef.2.2)

/-- Lemma 8.3.1: (Completeness of ground resolution) The ground
    resolution method is complete for ground clauses. -/
@[blueprint "chap8__lemma_8_3_1" (main := true)]
theorem ground_resolution_completeness
    {L : Language} (hNoEq : L.withoutEquality)
    (hL : L.withoutEquality)
    (S : List (FOClause L hNoEq))
    (hGround : ∀ c ∈ S, FOClause.isGround hNoEq c)
    (hUnsat : GroundClauseSet.isUnsatisfiable (hNoEq := hNoEq) S) :
    ∃ T : FOResolutionTree L hNoEq,
      T.isRefutation (hNoEq := hNoEq) (fun c => c ∈ S)

-- ===================================================================
-- Example 8.3.1: Refutation root is empty clause
-- ===================================================================

-- Helper lemmas for concrete term discrimination














-- Step labels for the intermediate resolution steps






/-- Example 8.3.1 (companion): The root label of exGroundResolution_refutation is
    the empty clause, confirming the refutation is valid. -/
@[blueprint "chap8__example_8_3_1"]
theorem exGroundResolution_refutation_label_empty :
    FOResolutionTree.labelSpec (hNoEq := by rfl) exGroundResolution_refutation []

end LCS.FOResolution.GroundResolution
end

