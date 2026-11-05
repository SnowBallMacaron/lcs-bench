import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions
import LCS.CutElim.Interpolation.ConstantSubstitution
import LCS.CutElim.Interpolation.VariableSubstitution
import LCS.CutElim.Interpolation.RuleSubstitution
import LCS.CutElim.Interpolation.InterpolantRepair
import LCS.CutElim.Interpolation.QuantifierCases
import LCS.CutElim.Interpolation.KeyLemma
import LCS.CutElim.Interpolation.FreshPredicate
import Attach
import LCS.CutElim.Interpolation.Craig.ProofsStamp

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka
-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
namespace CraigFreshBot

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Lower every indexed one-premise LK rule from the fresh-bottom language.
The proof-wide freshness fact is used only for the instantiating terms of
quantifier rules; the replacement formula is closed, so eigenvariable
freshness is preserved directly. -/
def freshLower_folkStep1_sharedPredFalse {L : Language}
    (P : L.predSymbols) (v : Nat)
    {prem conc : Sequent (FreshBotLanguage L)}
    (rule : FOLKStep1 prem conc)
    (hvar : rule.varNotOccurs v) :
    FOLKStep1
      (freshLowerSequent (sharedPredFalse P v) prem)
      (freshLowerSequent (sharedPredFalse P v) conc) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList,
      List.map_cons] using
      (FOLKStep1.weakenLeft
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | weakenRight A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.weakenRight
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | contractLeft A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList,
      List.map_cons] using
      (FOLKStep1.contractLeft
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | contractRight A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.contractRight
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | exchangeLeft Γ A B Δ Λ =>
    simpa only [freshLowerSequent, freshLowerList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.exchangeLeft
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Δ)
        (freshLowerList (sharedPredFalse P v) Λ))
  | exchangeRight Γ Δ A B Λ =>
    simpa only [freshLowerSequent, freshLowerList, List.map_append,
      List.map_cons, List.map_nil] using
      (FOLKStep1.exchangeRight
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ)
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Λ))
  | andLeftL A B Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_cons] using
      (FOLKStep1.andLeftL
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | andLeftR A B Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_cons] using
      (FOLKStep1.andLeftR
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | orRightL A B Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.orRightL
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | orRightR A B Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.orRightR
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | implRight A B Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.implRight
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerFormula (sharedPredFalse P v) B)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | negLeft A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.negLeft
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | negRight A Γ Δ =>
    simpa only [freshLowerSequent, freshLowerList, freshLowerFormula,
      List.map_append, List.map_cons, List.map_nil] using
      (FOLKStep1.negRight
        (freshLowerFormula (sharedPredFalse P v) A)
        (freshLowerList (sharedPredFalse P v) Γ)
        (freshLowerList (sharedPredFalse P v) Δ))
  | allLeft t x A Γ Δ hfree =>
    exact freshLower_allLeft L P v t x A Γ Δ hfree hvar
  | allRight y x A Γ Δ hfresh hfreeFor =>
    exact freshLower_allRight L P v y x A Γ Δ hfresh hfreeFor hvar
  | exLeft y x A Γ Δ hfresh hfreeFor =>
    exact freshLower_exLeft L P v y x A Γ Δ hfresh hfreeFor hvar
  | exRight t x A Γ Δ hfree =>
    exact freshLower_exRight L P v t x A Γ Δ hfree hvar
-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Lower every indexed two-premise LK rule from the fresh-bottom language.
No extra freshness premise is needed because these rules carry no
instantiating terms or eigenvariable side conditions. -/
def freshLower_folkStep2_sharedPredFalse {L : Language}
    (P : L.predSymbols) (v : Nat)
    {prem₁ prem₂ conc : Sequent (FreshBotLanguage L)}
    (rule : FOLKStep2 prem₁ prem₂ conc) :
    FOLKStep2
      (freshLowerSequent (sharedPredFalse P v) prem₁)
      (freshLowerSequent (sharedPredFalse P v) prem₂)
      (freshLowerSequent (sharedPredFalse P v) conc) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    let lowered := FOLKStep2.cut
      (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ)
      (freshLowerList (sharedPredFalse P v) Λ)
      (freshLowerList (sharedPredFalse P v) Θ)
    exact reindexFOLKStep2 lowered
      (by simp only [freshLowerSequent, freshLowerList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLowerSequent, freshLowerList, List.map_cons])
      (by simp only [freshLowerSequent, freshLowerList, List.map_append])
  | andRight A B Γ Δ =>
    let lowered := FOLKStep2.andRight
      (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerFormula (sharedPredFalse P v) B)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ)
    exact reindexFOLKStep2 lowered
      (by simp only [freshLowerSequent, freshLowerList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLowerSequent, freshLowerList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLowerSequent, freshLowerList, freshLowerFormula,
        List.map_append, List.map_cons, List.map_nil])
  | orLeft A B Γ Δ =>
    let lowered := FOLKStep2.orLeft
      (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerFormula (sharedPredFalse P v) B)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ)
    exact reindexFOLKStep2 lowered
      (by simp only [freshLowerSequent, freshLowerList, List.map_cons])
      (by simp only [freshLowerSequent, freshLowerList, List.map_cons])
      (by simp only [freshLowerSequent, freshLowerList, freshLowerFormula,
        List.map_cons])
  | implLeft A B Γ Δ Λ Θ =>
    let lowered := FOLKStep2.implLeft
      (freshLowerFormula (sharedPredFalse P v) A)
      (freshLowerFormula (sharedPredFalse P v) B)
      (freshLowerList (sharedPredFalse P v) Γ)
      (freshLowerList (sharedPredFalse P v) Δ)
      (freshLowerList (sharedPredFalse P v) Λ)
      (freshLowerList (sharedPredFalse P v) Θ)
    exact reindexFOLKStep2 lowered
      (by simp only [freshLowerSequent, freshLowerList, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [freshLowerSequent, freshLowerList, List.map_cons])
      (by simp only [freshLowerSequent, freshLowerList, freshLowerFormula,
        List.map_append, List.map_cons])

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Structural lowering of an indexed LK⊥ proof tree in the fresh-bottom
language. Ordinary axiom leaves remain exact axioms, the distinguished
bottom leaf becomes `sharedPredFalseRefutation`, and every internal rule is
replayed with its exact lowered indices. -/
noncomputable def freshLower_folkBotProofTree_sharedPredFalse {L : Language}
    (P : L.predSymbols) (v : Nat)
    {s : Sequent (FreshBotLanguage L)}
    (T : FOLKBotProofTree
      (freshBot (L := L)) (freshBot_arity (L := L)) s)
    (hvar : T.varNotOccurs v) :
    FOLKProofTree
      (freshLowerSequent (sharedPredFalse P v) s) := by
  let rec transform
      {q : Sequent (FreshBotLanguage L)}
      (U : FOLKBotProofTree
        (freshBot (L := L)) (freshBot_arity (L := L)) q)
      (hU : U.varNotOccurs v) :
      FOLKProofTree
        (freshLowerSequent (sharedPredFalse P v) q) :=
    match U with
    | .axiom_ q hax => by
      by_cases hFolk : isFOLKAxiom q
      · exact FOLKProofTree.axiom_ _
          (freshLower_isFOLKAxiom_sharedPredFalse P v q hFolk)
      · have hBot := hax.resolve_left hFolk
        simpa only [freshLowerSequent, freshLowerList, hBot.1, hBot.2,
          List.map_cons, List.map_nil, freshLowerFormula_freshBot] using
          sharedPredFalseRefutation P v
    | .onePremise rule t => by
      simp only [FOLKBotProofTree.varNotOccurs] at hU
      exact FOLKProofTree.onePremise
        (freshLower_folkStep1_sharedPredFalse P v rule hU.1)
        (transform t hU.2)
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKBotProofTree.varNotOccurs] at hU
      exact FOLKProofTree.twoPremise
        (freshLower_folkStep2_sharedPredFalse P v rule)
        (transform t₁ hU.2.1) (transform t₂ hU.2.2)
  exact transform T hvar

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- The result of structural lowering has exactly the lowered source
conclusion; no unindexed conclusion field is used. -/
@[simp]
theorem freshLower_folkBotProofTree_sharedPredFalse_conclusion
    {L : Language} (P : L.predSymbols) (v : Nat)
    {s : Sequent (FreshBotLanguage L)}
    (T : FOLKBotProofTree
      (freshBot (L := L)) (freshBot_arity (L := L)) s)
    (hvar : T.varNotOccurs v) :
    (freshLower_folkBotProofTree_sharedPredFalse P v T hvar).conclusion =
      freshLowerSequent (sharedPredFalse P v) T.conclusion :=
  rfl

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Choose one variable absent from both LK⊥ proof trees and lower both
trees using the same shared contradiction. This synchronization is what
keeps the two proof obligations about one and the same lowered interpolant. -/
theorem freshLower_folkBotProofTree_pair_sharedPredFalse
    {L : Language} (P : L.predSymbols)
    {s₁ s₂ : Sequent (FreshBotLanguage L)}
    (T₁ : FOLKBotProofTree
      (freshBot (L := L)) (freshBot_arity (L := L)) s₁)
    (T₂ : FOLKBotProofTree
      (freshBot (L := L)) (freshBot_arity (L := L)) s₂) :
    ∃ v,
      folkProvable
          (freshLowerSequent (sharedPredFalse P v) s₁) ∧
        folkProvable
          (freshLowerSequent (sharedPredFalse P v) s₂) := by
  let v :=
    Nat.max (folkBotProofAllMaxVar T₁)
      (folkBotProofAllMaxVar T₂) + 1
  have hv₁ : v > folkBotProofAllMaxVar T₁ := by
    dsimp only [v]
    exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have hv₂ : v > folkBotProofAllMaxVar T₂ := by
    dsimp only [v]
    exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
  have hvar₁ : T₁.varNotOccurs v :=
    T₁.varNotOccurs_of_gt v hv₁
  have hvar₂ : T₂.varNotOccurs v :=
    T₂.varNotOccurs_of_gt v hv₂
  exact
    ⟨v,
      ⟨freshLower_folkBotProofTree_sharedPredFalse P v T₁ hvar₁⟩,
      ⟨freshLower_folkBotProofTree_sharedPredFalse P v T₂ hvar₂⟩⟩

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Provability-level synchronized wrapper: unpack two fresh-bottom LK⊥
derivations, choose one proof-wide fresh variable for the pair, and lower
both derivations with the same shared contradiction. -/
theorem freshLower_lkBotProvable_pair_sharedPredFalse
    {L : Language} (P : L.predSymbols)
    {s₁ s₂ : Sequent (FreshBotLanguage L)}
    (h₁ : lkBotProvable
      (freshBot (L := L)) (freshBot_arity (L := L)) s₁)
    (h₂ : lkBotProvable
      (freshBot (L := L)) (freshBot_arity (L := L)) s₂) :
    ∃ v,
      folkProvable
          (freshLowerSequent (sharedPredFalse P v) s₁) ∧
        folkProvable
          (freshLowerSequent (sharedPredFalse P v) s₂) := by
  rcases h₁ with ⟨T₁⟩
  rcases h₂ with ⟨T₂⟩
  exact freshLower_folkBotProofTree_pair_sharedPredFalse P T₁ T₂

end CraigFreshBot
end LCS.CutElim.Interpolation
end

section
namespace LCS.CutElim.Interpolation
open Classical
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.CutElim.LK
open LCS.CutElim.LKe
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen.Hintikka
-- ATTACH-BLOCKER: variable
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Internal existence form of Craig interpolation in the common-predicate
case.  The proof adjoins a genuinely fresh nullary predicate, applies the
key lemma there, and then lowers both proof obligations simultaneously by
replacing the fresh predicate with Gallier's contradiction over `P`. -/
theorem craig_interpolant_common_pred_exists_cutFree {L : Language}
    (A B : FormulaN L)
    (hProv : folkCutFreeProvable { antecedent := [A], succedent := [B] })
    (P : L.predSymbols) (hPA : formulaPredSymbolsN A P)
    (hPB : formulaPredSymbolsN B P) :
    ∃ C, IsImplicationInterpolant A B C := by
  let s : Sequent L := { antecedent := [A], succedent := [B] }
  let sFresh : Sequent (CraigFreshBot.FreshBotLanguage L) :=
    CraigFreshBot.freshLiftSequent s
  let p : SequentPartition sFresh :=
    { gamma1 := [CraigFreshBot.freshLiftFormula A]
      delta1 := []
      gamma2 := []
      delta2 := [CraigFreshBot.freshLiftFormula B]
      gamma_partition := by
        exact .left _ .nil
      delta_partition := by
        exact .right _ .nil }
  have hLift : folkCutFreeProvable sFresh := by
    exact CraigFreshBot.freshLift_folkCutFreeProvable s
      (by simpa only [s] using hProv)
  let C₀ : FormulaN (CraigFreshBot.FreshBotLanguage L) :=
    @interpolation_key_lemma_witness_cutFree
      (CraigFreshBot.FreshBotLanguage L)
      CraigFreshBot.freshBot CraigFreshBot.freshBot_arity
      sFresh hLift p
  have hC₀ :
      IsInterpolant CraigFreshBot.freshBot CraigFreshBot.freshBot_arity
        p C₀ := by
    dsimp only [C₀]
    exact interpolation_key_lemma_witness_cutFree_spec sFresh hLift p
  rcases
      CraigFreshBot.freshLower_lkBotProvable_pair_sharedPredFalse
        P hC₀.left_provable hC₀.right_provable with
    ⟨v, hLeft, hRight⟩
  let C : FormulaN L :=
    CraigFreshBot.freshLowerFormula
      (CraigFreshBot.sharedPredFalse P v) C₀
  refine ⟨C, ?_⟩
  refine
    { left_provable := ?_
      right_provable := ?_
      pred_common := ?_
      const_common := ?_
      fv_common := ?_ }
  · simpa only [C, p, CraigFreshBot.freshLowerSequent,
      CraigFreshBot.freshLowerList, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil,
      CraigFreshBot.freshLowerFormula_lift] using hLeft
  · simpa only [C, p, CraigFreshBot.freshLowerSequent,
      CraigFreshBot.freshLowerList, List.map_cons, List.map_nil,
      List.nil_append, List.append_nil,
      CraigFreshBot.freshLowerFormula_lift] using hRight
  · intro Q hQ
    rcases
        (CraigFreshBot.freshLowerFormula_sharedPredFalse_predSymbols
          P Q v C₀).mp hQ with
      hOld | ⟨hBot, hQP⟩
    · have hCommon := hC₀.pred_common (.inl Q) hOld
          (by
            intro h
            cases h)
      constructor
      · have hA := hCommon.1
        change
          ∃ F ∈ [CraigFreshBot.freshLiftFormula A],
            formulaPredSymbolsN F (.inl Q) at hA
        rcases hA with ⟨F, hF, hFQ⟩
        have hFA : F = CraigFreshBot.freshLiftFormula A :=
          List.mem_singleton.mp hF
        subst F
        exact
          (CraigFreshBot.freshLiftFormula_predSymbols_inl A Q).mp hFQ
      · have hB := hCommon.2
        change
          ∃ F ∈ [CraigFreshBot.freshLiftFormula B],
            formulaPredSymbolsN F (.inl Q) at hB
        rcases hB with ⟨F, hF, hFQ⟩
        have hFB : F = CraigFreshBot.freshLiftFormula B :=
          List.mem_singleton.mp hF
        subst F
        exact
          (CraigFreshBot.freshLiftFormula_predSymbols_inl B Q).mp hFQ
    · subst Q
      exact ⟨hPA, hPB⟩
  · intro c hc
    have hOld :
        formulaConstSymbolsN C₀ c :=
      CraigFreshBot.freshLowerFormula_sharedPredFalse_constSymbols
        P v C₀ c hc
    have hCommon := hC₀.const_common c hOld
    constructor
    · simpa only [p, listFormulaConstSymbols, List.append_nil,
        List.mem_singleton, exists_eq_left,
        CraigFreshBot.freshLiftFormula_constSymbols] using hCommon.1
    · simpa only [p, listFormulaConstSymbols, List.nil_append,
        List.mem_singleton, exists_eq_left,
        CraigFreshBot.freshLiftFormula_constSymbols] using hCommon.2
  · intro x hx
    have hOld : formulaFVN C₀ x :=
      CraigFreshBot.freshLowerFormula_sharedPredFalse_fv P v C₀ x hx
    have hCommon := hC₀.fv_common x hOld
    constructor
    · simpa only [p, listFormulaFV, List.append_nil,
        List.mem_singleton, exists_eq_left,
        CraigFreshBot.freshLiftFormula_fv] using hCommon.1
    · simpa only [p, listFormulaFV, List.nil_append,
        List.mem_singleton, exists_eq_left,
        CraigFreshBot.freshLiftFormula_fv] using hCommon.2

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Theorem 6.5.1 (part a, required helper): If `A ⊃ B` is LK-provable
and `A` and `B` share a predicate symbol `P`, constructs an
interpolant `C` of `A ⊃ B` — a formula whose predicate, constant
symbols and free variables all occur in both `A` and `B`, and such
that both `A → C` and `C → B` are LK-provable. -/
noncomputable def craig_interpolant_common_pred_cutFree {L : Language}
    (A B : FormulaN L)
    (hProv : folkCutFreeProvable { antecedent := [A], succedent := [B] })
    (P : L.predSymbols) (hPA : formulaPredSymbolsN A P) (hPB : formulaPredSymbolsN B P) :
    FormulaN L :=
  Classical.choose
    (craig_interpolant_common_pred_exists_cutFree A B hProv P hPA hPB)

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Spec for `craig_interpolant_common_pred_cutFree`: the constructed formula
satisfies `IsImplicationInterpolant`. -/
theorem craig_interpolant_common_pred_cutFree_spec {L : Language}
    (A B : FormulaN L)
    (hProv : folkCutFreeProvable { antecedent := [A], succedent := [B] })
    (P : L.predSymbols) (hPA : formulaPredSymbolsN A P) (hPB : formulaPredSymbolsN B P) :
    IsImplicationInterpolant A B
      (craig_interpolant_common_pred_cutFree A B hProv P hPA hPB) :=
  Classical.choose_spec
    (craig_interpolant_common_pred_exists_cutFree A B hProv P hPA hPB)

/-- Internal existence form of Craig interpolation in the common-predicate
case.  The proof adjoins a genuinely fresh nullary predicate, applies the
key lemma there, and then lowers both proof obligations simultaneously by
replacing the fresh predicate with Gallier's contradiction over `P`. -/
@[blueprint "chap6__theorem_6_5_1" (main := true)]
theorem craig_interpolant_common_pred_exists {L : Language}
    (A B : FormulaN L) (hNoEq : L.withoutEquality)
    (hProv : folkProvable { antecedent := [A], succedent := [B] })
    (P : L.predSymbols) (hPA : formulaPredSymbolsN A P)
    (hPB : formulaPredSymbolsN B P) :
    ∃ C, IsImplicationInterpolant A B C 

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Theorem 6.5.1 (part a, required helper): If `A ⊃ B` is LK-provable
and `A` and `B` share a predicate symbol `P`, constructs an
interpolant `C` of `A ⊃ B` — a formula whose predicate, constant
symbols and free variables all occur in both `A` and `B`, and such
that both `A → C` and `C → B` are LK-provable. -/
noncomputable def craig_interpolant_common_pred {L : Language}
    (A B : FormulaN L) (hNoEq : L.withoutEquality)
    (hProv : folkProvable { antecedent := [A], succedent := [B] })
    (P : L.predSymbols) (hPA : formulaPredSymbolsN A P) (hPB : formulaPredSymbolsN B P) :
    FormulaN L :=
  Classical.choose
    (craig_interpolant_common_pred_exists A B hNoEq hProv P hPA hPB)

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Spec for `craig_interpolant_common_pred`: the constructed formula
satisfies `IsImplicationInterpolant`. -/
theorem craig_interpolant_common_pred_spec {L : Language}
    (A B : FormulaN L) (hNoEq : L.withoutEquality)
    (hProv : folkProvable { antecedent := [A], succedent := [B] })
    (P : L.predSymbols) (hPA : formulaPredSymbolsN A P) (hPB : formulaPredSymbolsN B P) :
    IsImplicationInterpolant A B
      (craig_interpolant_common_pred A B hNoEq hProv P hPA hPB) :=
  Classical.choose_spec
    (craig_interpolant_common_pred_exists A B hNoEq hProv P hPA hPB)

-- ===================================================================
-- Theorem 6.5.1 (part b): craig_interpolation_no_common_pred
-- ===================================================================

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Internal cut-free form of Theorem 6.5.1(b), used by the staged
combined Craig interpolation API below. -/
theorem craig_interpolation_no_common_pred_of_cutFree {L : Language}
    (A B : FormulaN L)
    (hNoEq : L.withoutEquality)
    (hProv : folkCutFreeProvable { antecedent := [A], succedent := [B] })
    (hNoPred : ∀ P : L.predSymbols, ¬ (formulaPredSymbolsN A P ∧ formulaPredSymbolsN B P)) :
    folkProvable { antecedent := [A], succedent := [] } ∨
    folkProvable { antecedent := [], succedent := [B] } := by
  have hANoEq : formulaNoEq A :=
    validBridgeFormulaNoEq_of_false hNoEq A
  have hBNoEq : formulaNoEq B :=
    validBridgeFormulaNoEq_of_false hNoEq B
  have hPredNonempty : Nonempty L.predSymbols :=
    Classical.byContradiction fun hEmpty =>
      formula_empty_pred_no_base hEmpty A hANoEq
  rcases hPredNonempty with ⟨P⟩
  let s : Sequent L := { antecedent := [A], succedent := [B] }
  let sFresh : Sequent (CraigFreshBot.FreshBotLanguage L) :=
    CraigFreshBot.freshLiftSequent s
  let p : SequentPartition sFresh :=
    { gamma1 := [CraigFreshBot.freshLiftFormula A]
      delta1 := []
      gamma2 := []
      delta2 := [CraigFreshBot.freshLiftFormula B]
      gamma_partition := by
        exact .left _ .nil
      delta_partition := by
        exact .right _ .nil }
  have hLift : folkCutFreeProvable sFresh := by
    exact CraigFreshBot.freshLift_folkCutFreeProvable s
      (by simpa only [s] using hProv)
  let C : FormulaN (CraigFreshBot.FreshBotLanguage L) :=
    @interpolation_key_lemma_witness_cutFree
      (CraigFreshBot.FreshBotLanguage L)
      CraigFreshBot.freshBot CraigFreshBot.freshBot_arity
      sFresh hLift p
  have hC :
      IsInterpolant CraigFreshBot.freshBot CraigFreshBot.freshBot_arity
        p C := by
    dsimp only [C]
    exact interpolation_key_lemma_witness_cutFree_spec sFresh hLift p
  have hOnlyBot :
      ∀ Q : (CraigFreshBot.FreshBotLanguage L).predSymbols,
        formulaPredSymbolsN C Q → Q = CraigFreshBot.freshBot := by
    intro Q hQ
    cases Q with
    | inl Q =>
        have hCommon := hC.pred_common (.inl Q) hQ
          (by
            intro h
            cases h)
        have hQA : formulaPredSymbolsN A Q := by
          have hLeft := hCommon.1
          change
            ∃ F ∈ [CraigFreshBot.freshLiftFormula A],
              formulaPredSymbolsN F (.inl Q) at hLeft
          rcases hLeft with ⟨F, hF, hFQ⟩
          have hFA : F = CraigFreshBot.freshLiftFormula A :=
            List.mem_singleton.mp hF
          subst F
          exact
            (CraigFreshBot.freshLiftFormula_predSymbols_inl A Q).mp hFQ
        have hQB : formulaPredSymbolsN B Q := by
          have hRight := hCommon.2
          change
            ∃ F ∈ [CraigFreshBot.freshLiftFormula B],
              formulaPredSymbolsN F (.inl Q) at hRight
          rcases hRight with ⟨F, hF, hFQ⟩
          have hFB : F = CraigFreshBot.freshLiftFormula B :=
            List.mem_singleton.mp hF
          subst F
          exact
            (CraigFreshBot.freshLiftFormula_predSymbols_inl B Q).mp hFQ
        exact (hNoPred Q ⟨hQA, hQB⟩).elim
    | inr u =>
        cases u
        rfl
  have hCNoEq : formulaNoEq C := by
    apply hC.no_eq
    intro F hF
    change
      F ∈ [CraigFreshBot.freshLiftFormula A,
        CraigFreshBot.freshLiftFormula B] at hF
    have hCases :
        F = CraigFreshBot.freshLiftFormula A ∨
          F = CraigFreshBot.freshLiftFormula B := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hF
    rcases hCases with hFA | hFB
    · subst F
      exact (CraigFreshBot.freshLiftFormula_noEq A).mpr hANoEq
    · subst F
      exact (CraigFreshBot.freshLiftFormula_noEq B).mpr hBNoEq
  rcases botFormula_lkBotProvable_or_lkBotRefutable C hOnlyBot hCNoEq with
    hCProv | hCRef
  · have hRight :=
      lkBot_twoPremise
        (.cut C [] [] [] [CraigFreshBot.freshLiftFormula B])
        hCProv hC.right_provable
    rcases
        CraigFreshBot.freshLower_lkBotProvable_pair_sharedPredFalse
          P hRight hRight with
      ⟨v, hLower, _⟩
    right
    simpa only [CraigFreshBot.freshLowerSequent,
      CraigFreshBot.freshLowerList, List.map_cons, List.map_nil,
      List.append_nil, List.nil_append,
      CraigFreshBot.freshLowerFormula_lift] using hLower
  · have hLeft :=
      lkBot_twoPremise
        (.cut C [CraigFreshBot.freshLiftFormula A] [] [] [])
        hC.left_provable hCRef
    rcases
        CraigFreshBot.freshLower_lkBotProvable_pair_sharedPredFalse
          P hLeft hLeft with
      ⟨v, hLower, _⟩
    left
    simpa only [CraigFreshBot.freshLowerSequent,
      CraigFreshBot.freshLowerList, List.map_cons, List.map_nil,
      List.append_nil, List.nil_append,
      CraigFreshBot.freshLowerFormula_lift] using hLower

/-- Theorem 6.5.1 (part b, required helper): Let `L` be a first-order
language without equality. If `A ⊃ B` is LK-provable and `A` and `B`
share no predicate symbol, then either `A →` is LK-provable or `→ B`
is LK-provable. -/
@[blueprint "chap6__theorem_6_5_1" (main := true)]
theorem craig_interpolation_no_common_pred {L : Language}
    (A B : FormulaN L)
    (hNoEq : L.withoutEquality)
    (hProv : folkProvable { antecedent := [A], succedent := [B] })
    (hNoPred : ∀ P : L.predSymbols, ¬ (formulaPredSymbolsN A P ∧ formulaPredSymbolsN B P)) :
    folkProvable { antecedent := [A], succedent := [] } ∨
    folkProvable { antecedent := [], succedent := [B] } 

-- ===================================================================
-- Theorem 6.5.1: craig_interpolation (combined)
-- ===================================================================

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Theorem 6.5.1: (Craig's interpolation theorem, without equality)
If `A ⊃ B` is LK-provable, then either (a) if `A` and `B` share a
predicate symbol, `craig_interpolation_cutFree` constructs an interpolant `C`
whose predicate, constant symbols and free variables occur in both
`A` and `B`, and both `A → C` and `C → B` are LK-provable; or (b) if
`A` and `B` share no predicate symbol, then either `A →` is
LK-provable or `→ B` is LK-provable. The (a) branch returns the
concrete interpolant formula as a function of the shared predicate
witness; the (b) branch is a genuine disjunction (textbook: "either
⊢ ¬A or ⊢ B"). -/
noncomputable def craig_interpolation_cutFree {L : Language}
    (A B : FormulaN L) (hProv : folkCutFreeProvable { antecedent := [A], succedent := [B] })
    (P : L.predSymbols) (hPA : formulaPredSymbolsN A P) (hPB : formulaPredSymbolsN B P) :
    FormulaN L :=
  craig_interpolant_common_pred_cutFree A B hProv P hPA hPB

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Spec for `craig_interpolation_cutFree`: in the shared-predicate case (a),
the constructed interpolant satisfies `IsImplicationInterpolant`;
in the no-shared-predicate case (b), either `A →` or `→ B` is
LK-provable. -/
theorem craig_interpolation_cutFree_spec {L : Language}
    (A B : FormulaN L) (hNoEq : L.withoutEquality)
    (hProv : folkCutFreeProvable { antecedent := [A], succedent := [B] }) :
    (∀ (P : L.predSymbols) (hPA : formulaPredSymbolsN A P) (hPB : formulaPredSymbolsN B P),
      IsImplicationInterpolant A B (craig_interpolation_cutFree A B hProv P hPA hPB)) ∧
    (∀ (_ : ∀ P : L.predSymbols, ¬ (formulaPredSymbolsN A P ∧ formulaPredSymbolsN B P)),
      folkProvable { antecedent := [A], succedent := [] } ∨
      folkProvable { antecedent := [], succedent := [B] }) :=
-- BEGIN PROOF
  ⟨fun P hPA hPB => craig_interpolant_common_pred_cutFree_spec A B hProv P hPA hPB,
   fun hNoPred =>
    craig_interpolation_no_common_pred_of_cutFree A B hNoEq hProv hNoPred⟩

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Theorem 6.5.1: (Craig's interpolation theorem, without equality)
If `A ⊃ B` is LK-provable, then either (a) if `A` and `B` share a
predicate symbol, `craig_interpolation` constructs an interpolant `C`
whose predicate, constant symbols and free variables occur in both
`A` and `B`, and both `A → C` and `C → B` are LK-provable; or (b) if
`A` and `B` share no predicate symbol, then either `A →` is
LK-provable or `→ B` is LK-provable. The (a) branch returns the
concrete interpolant formula as a function of the shared predicate
witness; the (b) branch is a genuine disjunction (textbook: "either
⊢ ¬A or ⊢ B"). -/
noncomputable def craig_interpolation {L : Language}
    (A B : FormulaN L) (hNoEq : L.withoutEquality)
    (hProv : folkProvable { antecedent := [A], succedent := [B] })
    (P : L.predSymbols) (hPA : formulaPredSymbolsN A P) (hPB : formulaPredSymbolsN B P) :
    FormulaN L :=
  craig_interpolant_common_pred A B hNoEq hProv P hPA hPB

-- ATTACH-BLOCKER: section variables: helper requires front context
/-- Spec for `craig_interpolation`: in the shared-predicate case (a),
the constructed interpolant satisfies `IsImplicationInterpolant`;
in the no-shared-predicate case (b), either `A →` or `→ B` is
LK-provable. -/
theorem craig_interpolation_spec {L : Language}
    (A B : FormulaN L) (hNoEq : L.withoutEquality)
    (hProv : folkProvable { antecedent := [A], succedent := [B] }) :
    (∀ (P : L.predSymbols) (hPA : formulaPredSymbolsN A P) (hPB : formulaPredSymbolsN B P),
      IsImplicationInterpolant A B (craig_interpolation A B hNoEq hProv P hPA hPB)) ∧
    (∀ (_ : ∀ P : L.predSymbols, ¬ (formulaPredSymbolsN A P ∧ formulaPredSymbolsN B P)),
      folkProvable { antecedent := [A], succedent := [] } ∨
      folkProvable { antecedent := [], succedent := [B] }) :=
-- BEGIN PROOF
  ⟨fun P hPA hPB => craig_interpolant_common_pred_spec A B hNoEq hProv P hPA hPB,
   fun hNoPred =>
    craig_interpolation_no_common_pred A B hNoEq hProv hNoPred⟩

end LCS.CutElim.Interpolation
end

