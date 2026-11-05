import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.Partitions
import LCS.CutElim.Interpolation.ConstantSubstitution
import LCS.CutElim.Interpolation.VariableSubstitution
import LCS.CutElim.Interpolation.RuleSubstitution

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
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

theorem termSubstConst_roundtrip {L : Language}
    (t : Term L) (z : Nat) (c : L.constSymbols) (hfresh : z ∉ termFV t) :
    termSubst (termSubstConst t z c) (.const c) z = t := by
-- BEGIN PROOF
  induction t with
  | var x =>
    simp only [termSubstConst, termSubst]
    split
    · rename_i h; subst h; exact absurd rfl hfresh
    · rfl
  | const c' =>
    simp only [termSubstConst]
    split
    · rename_i h; subst h; simp [termSubst]
    · simp [termSubst]
  | func f ts ih =>
    simp only [termSubstConst, termSubst]
    congr 1; ext i
    exact ih i (fun h => hfresh ⟨i, h⟩)

theorem formulaSubstConst_roundtrip {L : Language}
    (A : FormulaN L) (z : Nat) (c : L.constSymbols)
    (hfreshFV : z ∉ formulaFVN A) (hfreshBV : z ∉ formulaBVN A) :
    formulaSubstN (formulaSubstConst A z c) (.const c) z = A := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [formulaSubstConst, formulaSubstN]
    congr 1; ext i
    exact termSubstConst_roundtrip (ts i) z c (fun h => hfreshFV ⟨i, h⟩)
  | eq_ _ t1 t2 =>
    simp only [formulaSubstConst, formulaSubstN]; congr 1
    · exact termSubstConst_roundtrip t1 z c (fun h => hfreshFV (Or.inl h))
    · exact termSubstConst_roundtrip t2 z c (fun h => hfreshFV (Or.inr h))
  | conj A B ihA ihB =>
    simp only [formulaSubstConst, formulaSubstN]; congr 1
    · exact ihA (fun h => hfreshFV (Or.inl h)) (fun h => hfreshBV (Or.inl h))
    · exact ihB (fun h => hfreshFV (Or.inr h)) (fun h => hfreshBV (Or.inr h))
  | disj A B ihA ihB =>
    simp only [formulaSubstConst, formulaSubstN]; congr 1
    · exact ihA (fun h => hfreshFV (Or.inl h)) (fun h => hfreshBV (Or.inl h))
    · exact ihB (fun h => hfreshFV (Or.inr h)) (fun h => hfreshBV (Or.inr h))
  | impl A B ihA ihB =>
    simp only [formulaSubstConst, formulaSubstN]; congr 1
    · exact ihA (fun h => hfreshFV (Or.inl h)) (fun h => hfreshBV (Or.inl h))
    · exact ihB (fun h => hfreshFV (Or.inr h)) (fun h => hfreshBV (Or.inr h))
  | neg A ih =>
    simp only [formulaSubstConst, formulaSubstN]; congr 1
    exact ih hfreshFV hfreshBV
  | all y A ih =>
    simp only [formulaSubstConst, formulaSubstN]
    have hzy : z ≠ y := fun h => hfreshBV (by rw [h]; exact Or.inr rfl)
    simp [hzy]; congr 1
    exact ih (fun h => hfreshFV ⟨h, hzy⟩)
             (fun h => hfreshBV (Or.inl h))
  | ex y A ih =>
    simp only [formulaSubstConst, formulaSubstN]
    have hzy : z ≠ y := fun h => hfreshBV (by rw [h]; exact Or.inr rfl)
    simp [hzy]; congr 1
    exact ih (fun h => hfreshFV ⟨h, hzy⟩)
             (fun h => hfreshBV (Or.inl h))

theorem termSubstConst_no_const {L : Language}
    (t : Term L) (z : Nat) (c : L.constSymbols)
    (hNoConst : ¬ termConstSymbols t c) :
    termSubstConst t z c = t := by
-- BEGIN PROOF
  induction t with
  | var _ => simp [termSubstConst]
  | const d =>
    simp only [termSubstConst]
    split
    · rename_i h; subst h; exact absurd rfl hNoConst
    · rfl
  | func f ts ih =>
    simp only [termSubstConst]; congr 1; ext i
    exact ih i (fun h => hNoConst ⟨i, h⟩)

theorem formulaSubstConst_no_const {L : Language}
    (A : FormulaN L) (z : Nat) (c : L.constSymbols) (hNoConst : ¬ formulaConstSymbolsN A c) :
    formulaSubstConst A z c = A := by
-- BEGIN PROOF
  induction A with
  | predN P ts =>
    simp only [formulaSubstConst]; congr 1; ext i
    exact termSubstConst_no_const (ts i) z c (fun h => hNoConst ⟨i, h⟩)
  | eq_ _ t1 t2 =>
    simp only [formulaSubstConst]; congr 1
    · exact termSubstConst_no_const t1 z c (fun h => hNoConst (Or.inl h))
    · exact termSubstConst_no_const t2 z c (fun h => hNoConst (Or.inr h))
  | conj A B ihA ihB =>
    simp only [formulaSubstConst]; congr 1
    · exact ihA (fun h => hNoConst (Or.inl h))
    · exact ihB (fun h => hNoConst (Or.inr h))
  | disj A B ihA ihB =>
    simp only [formulaSubstConst]; congr 1
    · exact ihA (fun h => hNoConst (Or.inl h))
    · exact ihB (fun h => hNoConst (Or.inr h))
  | impl A B ihA ihB =>
    simp only [formulaSubstConst]; congr 1
    · exact ihA (fun h => hNoConst (Or.inl h))
    · exact ihB (fun h => hNoConst (Or.inr h))
  | neg A ih =>
    simp only [formulaSubstConst]; congr 1; exact ih hNoConst
  | all x A ih =>
    simp only [formulaSubstConst]; congr 1; exact ih hNoConst
  | ex x A ih =>
    simp only [formulaSubstConst]; congr 1; exact ih hNoConst

theorem list_map_formulaSubstConst_no_const {L : Language}
    (fs : List (FormulaN L)) (z : Nat) (c : L.constSymbols)
    (hNoConst : ∀ F ∈ fs, ¬ formulaConstSymbolsN F c) :
    fs.map (fun A => formulaSubstConst A z c) = fs := by
-- BEGIN PROOF
  induction fs with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons]
    rw [formulaSubstConst_no_const hd z c (hNoConst hd (List.Mem.head _)),
        ih (fun F hF => hNoConst F (List.Mem.tail _ hF))]

theorem sequentSubstConst_append_single {L : Language}
    (Γ Δ : List (FormulaN L)) (C : FormulaN L) (z : Nat) (c : L.constSymbols)
    (hNoConst : ∀ F ∈ Γ ++ Δ, ¬ formulaConstSymbolsN F c) :
    sequentSubstConst ⟨Γ, Δ ++ [C]⟩ z c = ⟨Γ, Δ ++ [formulaSubstConst C z c]⟩ := by
-- BEGIN PROOF
  simp only [sequentSubstConst]
  congr 1
  · exact list_map_formulaSubstConst_no_const Γ z c
      (fun F hF => hNoConst F (List.mem_append_left _ hF))
  · rw [List.map_append, List.map_cons, List.map_nil]
    congr 1
    exact list_map_formulaSubstConst_no_const Δ z c
      (fun F hF => hNoConst F (List.mem_append_right _ hF))

theorem sequentSubstConst_prepend_single {L : Language}
    (Γ Δ : List (FormulaN L)) (C : FormulaN L) (z : Nat) (c : L.constSymbols)
    (hNoConst : ∀ F ∈ Γ ++ Δ, ¬ formulaConstSymbolsN F c) :
    sequentSubstConst ⟨[C] ++ Γ, Δ⟩ z c = ⟨[formulaSubstConst C z c] ++ Γ, Δ⟩ := by
-- BEGIN PROOF
  simp only [sequentSubstConst, List.map_append, List.map_cons, List.map_nil]
  congr 1
  · congr 1
    exact list_map_formulaSubstConst_no_const Γ z c
      (fun F hF => hNoConst F (List.mem_append_left _ hF))
  · exact list_map_formulaSubstConst_no_const Δ z c
      (fun F hF => hNoConst F (List.mem_append_right _ hF))

theorem listFormulaAllMaxVar_mem_le {L : Language}
    (fs : List (FormulaN L)) (F : FormulaN L) (hF : F ∈ fs) :
    formulaAllMaxVar F ≤ listFormulaAllMaxVar fs := by
  unfold listFormulaAllMaxVar
  exact foldl_max_mem_le _ 0 _
    (List.mem_map.mpr ⟨F, hF, rfl⟩)

theorem formulaVarNotOccurs_of_gt {L : Language}
    (A : FormulaN L) (z : Nat) (hz : z > formulaAllMaxVar A) :
    formulaVarNotOccurs A z :=
  ⟨formulaAllMaxVar_gt_no_fv A z hz,
    formulaAllMaxVar_gt_no_bv A z hz⟩

theorem sequentVarNotOccurs_of_gt {L : Language}
    (s : Sequent L) (z : Nat) (hz : z > sequentAllMaxVar s) :
    sequentVarNotOccurs s z := by
  intro F hF
  rcases List.mem_append.mp hF with hΓ | hΔ
  · exact formulaVarNotOccurs_of_gt F z
      (Nat.lt_of_le_of_lt
        (Nat.le_trans
          (listFormulaAllMaxVar_mem_le s.antecedent F hΓ)
          (Nat.le_max_left _ _))
        hz)
  · exact formulaVarNotOccurs_of_gt F z
      (Nat.lt_of_le_of_lt
        (Nat.le_trans
          (listFormulaAllMaxVar_mem_le s.succedent F hΔ)
          (Nat.le_max_right _ _))
        hz)

/-- An upper bound on all variables mentioned by a one-premise LK rule,
including its premise, conclusion, eigenvariables, binders, terms, and
annotated formulae. -/
def folkStep1AllMaxVar {L : Language}
    {prem conc : Sequent L} (r : FOLKStep1 prem conc) : Nat :=
  Nat.max (sequentAllMaxVar prem)
    (Nat.max (sequentAllMaxVar conc)
      (match r with
      | .allLeft t x A _ _ _ =>
          Nat.max (termMaxVar t) (Nat.max x (formulaAllMaxVar A))
      | .allRight e x A _ _ _ _ =>
          Nat.max e (Nat.max x (formulaAllMaxVar A))
      | .exLeft e x A _ _ _ _ =>
          Nat.max e (Nat.max x (formulaAllMaxVar A))
      | .exRight t x A _ _ _ =>
          Nat.max (termMaxVar t) (Nat.max x (formulaAllMaxVar A))
      | _ => 0))

theorem folkStep1_varNotOccurs_of_gt {L : Language}
    {prem conc : Sequent L} (r : FOLKStep1 prem conc) (z : Nat)
    (hz : z > folkStep1AllMaxVar r) :
    r.varNotOccurs z := by
  have hPrem : z > sequentAllMaxVar prem :=
    Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hz
  have hConc : z > sequentAllMaxVar conc :=
    Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hz
  refine ⟨sequentVarNotOccurs_of_gt prem z hPrem,
    sequentVarNotOccurs_of_gt conc z hConc, ?_⟩
  cases r with
  | allLeft t x A Γ Δ hfree =>
      have hExtra :
          z > Nat.max (termMaxVar t) (Nat.max x (formulaAllMaxVar A)) :=
        Nat.lt_of_le_of_lt (by
          unfold folkStep1AllMaxVar
          exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hz
      exact
        ⟨termFV_gt_maxVar t z
            (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hExtra),
          fun hzx => by
            subst x
            exact Nat.not_lt.mpr
              (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
              hExtra,
          formulaVarNotOccurs_of_gt A z
            (Nat.lt_of_le_of_lt
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
              hExtra)⟩
  | allRight e x A Γ Δ hfresh hfree =>
      have hExtra :
          z > Nat.max e (Nat.max x (formulaAllMaxVar A)) :=
        Nat.lt_of_le_of_lt (by
          unfold folkStep1AllMaxVar
          exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hz
      exact
        ⟨fun hze => by
            subst e
            exact Nat.not_lt.mpr (Nat.le_max_left _ _) hExtra,
          fun hzx => by
            subst x
            exact Nat.not_lt.mpr
              (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
              hExtra,
          formulaVarNotOccurs_of_gt A z
            (Nat.lt_of_le_of_lt
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
              hExtra)⟩
  | exLeft e x A Γ Δ hfresh hfree =>
      have hExtra :
          z > Nat.max e (Nat.max x (formulaAllMaxVar A)) :=
        Nat.lt_of_le_of_lt (by
          unfold folkStep1AllMaxVar
          exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hz
      exact
        ⟨fun hze => by
            subst e
            exact Nat.not_lt.mpr (Nat.le_max_left _ _) hExtra,
          fun hzx => by
            subst x
            exact Nat.not_lt.mpr
              (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
              hExtra,
          formulaVarNotOccurs_of_gt A z
            (Nat.lt_of_le_of_lt
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
              hExtra)⟩
  | exRight t x A Γ Δ hfree =>
      have hExtra :
          z > Nat.max (termMaxVar t) (Nat.max x (formulaAllMaxVar A)) :=
        Nat.lt_of_le_of_lt (by
          unfold folkStep1AllMaxVar
          exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hz
      exact
        ⟨termFV_gt_maxVar t z
            (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hExtra),
          fun hzx => by
            subst x
            exact Nat.not_lt.mpr
              (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
              hExtra,
          formulaVarNotOccurs_of_gt A z
            (Nat.lt_of_le_of_lt
              (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
              hExtra)⟩
  | weakenLeft | weakenRight | contractLeft | contractRight |
    exchangeLeft | exchangeRight | andLeftL | andLeftR | orRightL |
    orRightR | implRight | negLeft | negRight =>
      trivial

/-- An upper bound on all variables mentioned by a two-premise LK rule,
including its premises, conclusion, cut formula, and connective formulae. -/
def folkStep2AllMaxVar {L : Language}
    {prem1 prem2 conc : Sequent L} (r : FOLKStep2 prem1 prem2 conc) : Nat :=
  Nat.max (sequentAllMaxVar prem1)
    (Nat.max (sequentAllMaxVar prem2)
      (Nat.max (sequentAllMaxVar conc)
        (match r with
        | .cut A _ _ _ _ => formulaAllMaxVar A
        | .andRight A B _ _ | .orLeft A B _ _ =>
            Nat.max (formulaAllMaxVar A) (formulaAllMaxVar B)
        | .implLeft A B _ _ _ _ =>
            Nat.max (formulaAllMaxVar A) (formulaAllMaxVar B))))

theorem folkStep2_varNotOccurs_of_gt {L : Language}
    {prem1 prem2 conc : Sequent L} (r : FOLKStep2 prem1 prem2 conc) (z : Nat)
    (hz : z > folkStep2AllMaxVar r) :
    r.varNotOccurs z := by
  have hPrem1 : z > sequentAllMaxVar prem1 :=
    Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hz
  have hPrem2 : z > sequentAllMaxVar prem2 :=
    Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hz
  have hConc : z > sequentAllMaxVar conc :=
    Nat.lt_of_le_of_lt
      (Nat.le_trans
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _))
      hz
  refine ⟨sequentVarNotOccurs_of_gt prem1 z hPrem1,
    sequentVarNotOccurs_of_gt prem2 z hPrem2,
    sequentVarNotOccurs_of_gt conc z hConc, ?_⟩
  cases r with
  | cut A Γ Δ Λ Θ =>
      have hExtra : z > formulaAllMaxVar A :=
        Nat.lt_of_le_of_lt (by
          unfold folkStep2AllMaxVar
          exact Nat.le_trans
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
            (Nat.le_max_right _ _)) hz
      exact formulaVarNotOccurs_of_gt A z hExtra
  | andRight A B Γ Δ | orLeft A B Γ Δ =>
      have hExtra :
          z > Nat.max (formulaAllMaxVar A) (formulaAllMaxVar B) :=
        Nat.lt_of_le_of_lt (by
          unfold folkStep2AllMaxVar
          exact Nat.le_trans
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
            (Nat.le_max_right _ _)) hz
      exact
        ⟨formulaVarNotOccurs_of_gt A z
            (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hExtra),
          formulaVarNotOccurs_of_gt B z
            (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hExtra)⟩
  | implLeft A B Γ Δ Λ Θ =>
      have hExtra :
          z > Nat.max (formulaAllMaxVar A) (formulaAllMaxVar B) :=
        Nat.lt_of_le_of_lt (by
          unfold folkStep2AllMaxVar
          exact Nat.le_trans
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
            (Nat.le_max_right _ _)) hz
      exact
        ⟨formulaVarNotOccurs_of_gt A z
            (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hExtra),
          formulaVarNotOccurs_of_gt B z
            (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hExtra)⟩

/-- An upper bound on every variable appearing anywhere in an LK⊥ proof
tree, including rule annotations that need not occur in the root sequent. -/
def folkBotProofAllMaxVar {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0} :
    {s : Sequent L} → FOLKBotProofTree botP hBotArity s → Nat
  | s, .axiom_ _ _ => sequentAllMaxVar s
  | _, .onePremise rule t =>
      Nat.max (folkStep1AllMaxVar rule) (folkBotProofAllMaxVar t)
  | _, .twoPremise rule t1 t2 =>
      Nat.max (folkStep2AllMaxVar rule)
        (Nat.max (folkBotProofAllMaxVar t1)
          (folkBotProofAllMaxVar t2))

/-- The variable is absent from every sequent, rule annotation, and subtree
of an LK⊥ proof tree. This is the proof-wide freshness premise used by
Lemma 6.5.1 substitution. -/
def FOLKBotProofTree.varNotOccurs {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0} :
    {s : Sequent L} → FOLKBotProofTree botP hBotArity s → Nat → Prop
  | s, .axiom_ _ _, z => sequentVarNotOccurs s z
  | _, .onePremise rule t, z =>
      rule.varNotOccurs z ∧ t.varNotOccurs z
  | _, .twoPremise rule t1 t2, z =>
      rule.varNotOccurs z ∧ t1.varNotOccurs z ∧
        t2.varNotOccurs z

theorem FOLKBotProofTree.varNotOccurs_of_gt {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    {s : Sequent L} (T : FOLKBotProofTree botP hBotArity s) (z : Nat)
    (hz : z > folkBotProofAllMaxVar T) :
    T.varNotOccurs z := by
  induction T with
  | axiom_ s h =>
      exact sequentVarNotOccurs_of_gt s z hz
  | onePremise rule t ih =>
      exact
        ⟨folkStep1_varNotOccurs_of_gt rule z
            (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hz),
          ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hz)⟩
  | twoPremise rule t1 t2 ih1 ih2 =>
      exact
        ⟨folkStep2_varNotOccurs_of_gt rule z
            (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hz),
          ih1 (Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hz),
          ih2 (Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hz)⟩

theorem FOLKBotProofTree.exists_varNotOccurs {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    {s : Sequent L} (T : FOLKBotProofTree botP hBotArity s) :
    ∃ z, T.varNotOccurs z := by
  let z := folkBotProofAllMaxVar T + 1
  exact ⟨z, T.varNotOccurs_of_gt z (by omega)⟩

theorem FOLKBotProofTree.rootVarNotOccurs {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    {s : Sequent L} (T : FOLKBotProofTree botP hBotArity s) (z : Nat)
    (hz : T.varNotOccurs z) :
    sequentVarNotOccurs s z := by
  cases T with
  | axiom_ s h => exact hz
  | onePremise rule t =>
      exact hz.1.2.1
  | twoPremise rule t1 t2 =>
      exact hz.1.2.2.1

theorem sequentFreshAfterConst {L : Language}
    (q : Sequent L) (z e : Nat) (c : L.constSymbols)
    (he : ∀ F ∈ q.antecedent ++ q.succedent, e ∉ formulaFVN F)
    (hez : e ≠ z) :
    ∀ F ∈ (sequentSubstConst q z c).antecedent ++
        (sequentSubstConst q z c).succedent,
      e ∉ formulaFVN F := by
  intro F hF
  change F ∈
    q.antecedent.map (fun A => formulaSubstConst A z c) ++
      q.succedent.map (fun A => formulaSubstConst A z c) at hF
  rcases List.mem_append.mp hF with hF | hF
  · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
    exact formulaFV_formulaSubstConst G z c e hez
      (he G (List.mem_append.mpr (Or.inl hG)))
  · rcases List.mem_map.mp hF with ⟨G, hG, rfl⟩
    exact formulaFV_formulaSubstConst G z c e hez
      (he G (List.mem_append.mpr (Or.inr hG)))

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
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
section
variable (L : Language) (botP : L.predSymbols) (hBotArity : L.predArity botP = 0) (z : Nat) (c : L.constSymbols)

noncomputable def botConst_allLeft
    (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t₀ x A) (transformedTree : FOLKBotProofTree botP hBotArity (sequentSubstConst (Sequent.mk
      (formulaSubstN A t₀ x :: Γ) (Δ)) z c)) (hRuleNO : (FOLKStep1.allLeft t₀ x A Γ Δ hfree).varNotOccurs z)
    : FOLKBotProofTree botP hBotArity (sequentSubstConst (Sequent.mk (FormulaN.all x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t₀ z c) x (formulaSubstConst A z c) :=
    isFreeFor_constSubst A t₀ x z c hfree hNoZ
  have sub : FOLKBotProofTree botP hBotArity (Sequent.mk (formulaSubstN (formulaSubstConst A z c)
              (termSubstConst t₀ z c) x ::
            Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))) := by
    simpa [sequentSubstConst, formulaSubstConst_formulaSubst_comm A t₀ x z c hzx] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.allLeft
        (termSubstConst t₀ z c) x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree')
      sub

noncomputable def botConst_allRight
    (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (Γ) ++ (Δ ++ [FormulaN.all x A]) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e)
      x A) (transformedTree : FOLKBotProofTree botP hBotArity (sequentSubstConst (Sequent.mk (Γ) (Δ ++
      [formulaSubstN A (Term.var e) x])) z c)) (hRuleNO : (FOLKStep1.allRight e x A Γ Δ hfresh
      hfree).varNotOccurs z)
    : FOLKBotProofTree botP hBotArity (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.all x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using isFreeFor_constSubst A (.var e) x z c hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).antecedent ++
          (Sequent.mk (Γ.map (fun G => formulaSubstConst G z c)) (Δ.map (fun G => formulaSubstConst G z c) ++
              [FormulaN.all x (formulaSubstConst A z c)])).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk Γ (Δ ++ [FormulaN.all x A])) z e c hfresh
        (Ne.symm hze)
  have sub : FOLKBotProofTree botP hBotArity (Sequent.mk (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c) ++
            [formulaSubstN (formulaSubstConst A z c) (.var e) x])) := by
    simpa [sequentSubstConst, formulaSubstConst_formulaSubst_comm A (.var e) x z c hzx,
      termSubstConst] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.allRight e x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree')
      sub

noncomputable def botConst_exLeft
    (e : Nat) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfresh : ∀ (F :
      FormulaN L), F ∈ (FormulaN.ex x A :: Γ) ++ (Δ) → ¬e ∈ formulaFVN F) (hfree : isFreeForN (Term.var e) x
      A) (transformedTree : FOLKBotProofTree botP hBotArity (sequentSubstConst (Sequent.mk (formulaSubstN A
      (Term.var e) x :: Γ) (Δ)) z c)) (hRuleNO : (FOLKStep1.exLeft e x A Γ Δ hfresh hfree).varNotOccurs z)
    : FOLKBotProofTree botP hBotArity (sequentSubstConst (Sequent.mk (FormulaN.ex x A :: Γ) (Δ)) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hze : z ≠ e := hRuleNO.2.2.1
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (.var e) x (formulaSubstConst A z c) := by
    simpa [termSubstConst] using isFreeFor_constSubst A (.var e) x z c hfree hNoZ
  have hfresh' : ∀ F ∈ (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) ::
              Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).antecedent ++
          (Sequent.mk (FormulaN.ex x (formulaSubstConst A z c) :: Γ.map (fun G => formulaSubstConst G z c))
            (Δ.map (fun G => formulaSubstConst G z c))).succedent,
        e ∉ formulaFVN F := by
    simpa [sequentSubstConst, formulaSubstConst] using sequentFreshAfterConst
        (Sequent.mk (FormulaN.ex x A :: Γ) Δ) z e c hfresh
        (Ne.symm hze)
  have sub : FOLKBotProofTree botP hBotArity (Sequent.mk
          (formulaSubstN (formulaSubstConst A z c) (.var e) x :: Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))) := by
    simpa [sequentSubstConst, formulaSubstConst_formulaSubst_comm A (.var e) x z c hzx,
      termSubstConst] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.exLeft e x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c))
        hfresh' hfree')
      sub

noncomputable def botConst_exRight
    (t₀ : Term L) (x : Nat) (A : FormulaN L) (Γ : List (FormulaN L)) (Δ : List (FormulaN L)) (hfree :
      isFreeForN t₀ x A) (transformedTree : FOLKBotProofTree botP hBotArity (sequentSubstConst (Sequent.mk (Γ)
      (Δ ++ [formulaSubstN A t₀ x])) z c)) (hRuleNO : (FOLKStep1.exRight t₀ x A Γ Δ hfree).varNotOccurs z)
    : FOLKBotProofTree botP hBotArity (sequentSubstConst (Sequent.mk (Γ) (Δ ++ [FormulaN.ex x A])) z c) := by
  simp only [FOLKStep1.varNotOccurs] at hRuleNO
  have hzx : z ≠ x := hRuleNO.2.2.2.1
  have hNoZ : z ∉ formulaBVN A := hRuleNO.2.2.2.2.2
  have hfree' : isFreeForN (termSubstConst t₀ z c) x (formulaSubstConst A z c) :=
    isFreeFor_constSubst A t₀ x z c hfree hNoZ
  have sub : FOLKBotProofTree botP hBotArity (Sequent.mk (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c) ++ [formulaSubstN (formulaSubstConst A z c)
              (termSubstConst t₀ z c) x])) := by
    simpa [sequentSubstConst, formulaSubstConst_formulaSubst_comm A t₀ x z c hzx] using transformedTree
  simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.exRight
        (termSubstConst t₀ z c) x
        (formulaSubstConst A z c)
        (Γ.map (fun F => formulaSubstConst F z c))
        (Δ.map (fun F => formulaSubstConst F z c)) hfree')
      sub

noncomputable def botConst_oneRule
    (q : Sequent L) (prem : Sequent L) (rule : FOLKStep1 prem q) (hRuleNO : rule.varNotOccurs z)
      (transformedTree : FOLKBotProofTree botP hBotArity (sequentSubstConst prem z c))
    : FOLKBotProofTree botP hBotArity (sequentSubstConst q z c) := by
  cases rule with
  | weakenLeft A Γ Δ =>
    simpa [sequentSubstConst] using FOLKBotProofTree.onePremise
        (FOLKStep1.weakenLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | weakenRight A Γ Δ =>
    simpa [sequentSubstConst] using FOLKBotProofTree.onePremise
        (FOLKStep1.weakenRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | contractLeft A Γ Δ =>
    simpa [sequentSubstConst] using FOLKBotProofTree.onePremise
        (FOLKStep1.contractLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | contractRight A Γ Δ =>
    simpa [sequentSubstConst] using FOLKBotProofTree.onePremise
        (FOLKStep1.contractRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | exchangeLeft Γ A B Δ Λ =>
    simpa [sequentSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.exchangeLeft
          (Γ.map (fun F => formulaSubstConst F z c))
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | exchangeRight Γ Δ A B Λ =>
    simpa [sequentSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.exchangeRight
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Λ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | andLeftL A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.andLeftL
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | andLeftR A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.andLeftR
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | orRightL A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.orRightL
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | orRightR A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.orRightR
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | implRight A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise (FOLKStep1.implRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | negLeft A Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise
        (FOLKStep1.negLeft (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | negRight A Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.onePremise
        (FOLKStep1.negRight (formulaSubstConst A z c) (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree)
  | allLeft t₀ x A Γ Δ hfree =>
    exact botConst_allLeft L botP hBotArity z c t₀ x A Γ Δ hfree transformedTree hRuleNO
  | allRight e x A Γ Δ hfresh hfree =>
    exact botConst_allRight L botP hBotArity z c e x A Γ Δ hfresh hfree transformedTree hRuleNO
  | exLeft e x A Γ Δ hfresh hfree =>
    exact botConst_exLeft L botP hBotArity z c e x A Γ Δ hfresh hfree transformedTree hRuleNO
  | exRight t₀ x A Γ Δ hfree =>
    exact botConst_exRight L botP hBotArity z c t₀ x A Γ Δ hfree transformedTree hRuleNO

noncomputable def botConst_twoRule
    (q : Sequent L) (prem1 : Sequent L) (prem2 : Sequent L) (rule : FOLKStep2 prem1 prem2 q) (transformedTree₁
      : FOLKBotProofTree botP hBotArity (sequentSubstConst prem1 z c)) (transformedTree₂ : FOLKBotProofTree
      botP hBotArity (sequentSubstConst prem2 z c))
    : FOLKBotProofTree botP hBotArity (sequentSubstConst q z c) := by
  cases rule with
  | cut A Γ Δ Λ Θ =>
    simpa [sequentSubstConst] using FOLKBotProofTree.twoPremise (FOLKStep2.cut (formulaSubstConst A z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | andRight A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.twoPremise (FOLKStep2.andRight
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | orLeft A B Γ Δ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.twoPremise (FOLKStep2.orLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)
  | implLeft A B Γ Δ Λ Θ =>
    simpa [sequentSubstConst, formulaSubstConst] using FOLKBotProofTree.twoPremise (FOLKStep2.implLeft
          (formulaSubstConst A z c)
          (formulaSubstConst B z c)
          (Γ.map (fun F => formulaSubstConst F z c))
          (Δ.map (fun F => formulaSubstConst F z c))
          (Λ.map (fun F => formulaSubstConst F z c))
          (Θ.map (fun F => formulaSubstConst F z c)))
        (by simpa [sequentSubstConst] using transformedTree₁)
        (by simpa [sequentSubstConst] using transformedTree₂)

end
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
variable {L : Language} {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}

/-- Lemma 6.5.1 constant substitution lifted to LK⊥ proof trees. The
ordinary `folkProofSubstConst` cannot consume the special ⊥ axiom leaf,
so this adapter replays every indexed LK rule and preserves that leaf. -/
noncomputable def folkBotProofSubstConst {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    {s : Sequent L} (T : FOLKBotProofTree botP hBotArity s)
    (z : Nat) (c : L.constSymbols)
    (hNotOccurs : T.varNotOccurs z) :
    FOLKBotProofTree botP hBotArity (sequentSubstConst s z c) := by
  let rec transform {q : Sequent L}
      (U : FOLKBotProofTree botP hBotArity q)
      (hNO : U.varNotOccurs z) :
      FOLKBotProofTree botP hBotArity (sequentSubstConst q z c) :=
    match U with
    | .axiom_ q hax => by
      by_cases hFolk : isFOLKAxiom q
      · apply FOLKBotProofTree.axiom_ _ (Or.inl ?_)
        rcases hFolk with ⟨A, hΓ, hΔ⟩
        exact
          ⟨formulaSubstConst A z c,
            by simp [sequentSubstConst, hΓ],
            by simp [sequentSubstConst, hΔ]⟩
      · apply FOLKBotProofTree.axiom_ _ (Or.inr ?_)
        have hbot := hax.resolve_left hFolk
        rcases hbot with ⟨hΓ, hΔ⟩
        constructor
        · have hBotSubst :
              formulaSubstConst (botFormula botP hBotArity) z c =
                botFormula botP hBotArity :=
            formulaSubstConst_no_const _ z c (by
              intro hc
              rcases hc with ⟨i, _⟩
              exact Fin.elim0 (hBotArity ▸ i))
          simp [sequentSubstConst, hΓ, hBotSubst]
        · simp [sequentSubstConst, hΔ]
    | .onePremise rule t => by
      simp only [FOLKBotProofTree.varNotOccurs] at hNO
      rcases hNO with ⟨hRuleNO, hTreeNO⟩
      have transformedTree := transform t hTreeNO
      exact botConst_oneRule L botP hBotArity z c _ _ rule hRuleNO transformedTree
    | .twoPremise rule t₁ t₂ => by
      simp only [FOLKBotProofTree.varNotOccurs] at hNO
      rcases hNO with ⟨_, hTree₁NO, hTree₂NO⟩
      have transformedTree₁ := transform t₁ hTree₁NO
      have transformedTree₂ := transform t₂ hTree₂NO
      exact botConst_twoRule L botP hBotArity z c _ _ _ rule transformedTree₁ transformedTree₂
  exact transform T hNotOccurs

-- ===================================================================
-- Interpolant fix infrastructure (adapted to indexed types with botP/hBotArity)
-- ===================================================================

theorem interpolant_fix_one_const {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (Γ₁ Δ₁ Γ₂ Δ₂ : List (FormulaN L)) (C : FormulaN L) (c : L.constSymbols)
    (hLeft : lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C]⟩)
    (hRight : lkBotProvable botP hBotArity ⟨[C] ++ Γ₂, Δ₂⟩)
    (hNoConstLeft : ∀ F ∈ Γ₁ ++ Δ₁, ¬ formulaConstSymbolsN F c) :
    ∃ C' : FormulaN L,
      lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C']⟩ ∧
      lkBotProvable botP hBotArity ⟨[C'] ++ Γ₂, Δ₂⟩ ∧
      formulaPredSymbolsN C' = formulaPredSymbolsN C ∧
      (∀ d, formulaConstSymbolsN C' d → formulaConstSymbolsN C d ∧ d ≠ c) ∧
      (∀ v, formulaFVN C' v → formulaFVN C v) ∧
      (formulaNoEq C → formulaNoEq C') := by
  obtain ⟨tLeft⟩ := hLeft
  obtain ⟨z, hzTree⟩ := tLeft.exists_varNotOccurs
  have hzRoot : sequentVarNotOccurs
      (Sequent.mk Γ₁ (Δ₁ ++ [C])) z :=
    tLeft.rootVarNotOccurs z hzTree
  have hzC : formulaVarNotOccurs C z :=
    hzRoot C (by simp)
  let D := formulaSubstConst C z c
  let C' := FormulaN.all z D
  have hLeftSub :
      lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [D]⟩ := by
    have tLeftSub :=
      folkBotProofSubstConst tLeft z c hzTree
    rw [sequentSubstConst_append_single Γ₁ Δ₁ C z c hNoConstLeft]
      at tLeftSub
    exact ⟨by simpa [D] using tLeftSub⟩
  have hFreshConclusion :
      ∀ F ∈
          (Sequent.mk Γ₁ (Δ₁ ++ [C'])).antecedent ++
            (Sequent.mk Γ₁ (Δ₁ ++ [C'])).succedent,
        z ∉ formulaFVN F := by
    intro F hF
    change F ∈ Γ₁ ++ (Δ₁ ++ [C']) at hF
    rcases List.mem_append.mp hF with hΓ | hΔC
    · exact (hzRoot F (List.mem_append.mpr (Or.inl hΓ))).1
    · rcases List.mem_append.mp hΔC with hΔ | hC'
      · exact
          (hzRoot F
            (List.mem_append.mpr
              (Or.inr (List.mem_append.mpr (Or.inl hΔ))))).1
      · have hFC' : F = C' := by simpa using hC'
        subst F
        intro hv
        exact hv.2 rfl
  have hLeft' : lkBotProvable botP hBotArity
      ⟨Γ₁, Δ₁ ++ [C']⟩ := by
    apply lkBot_onePremise
      (FOLKStep1.allRight z z D Γ₁ Δ₁ hFreshConclusion
        (isFreeForN_var_self D z))
    simpa [C', formulaSubstN_var_self] using hLeftSub
  have hRight' : lkBotProvable botP hBotArity
      ⟨[C'] ++ Γ₂, Δ₂⟩ := by
    apply lkBot_onePremise
      (FOLKStep1.allLeft (.const c) z D Γ₂ Δ₂
        (isFreeFor_const c z D))
    simpa [C', D, formulaSubstConst_roundtrip C z c hzC.1 hzC.2]
      using hRight
  refine ⟨C', hLeft', hRight', ?_, ?_, ?_, ?_⟩
  · exact formulaPredSymbolsN_formulaSubstConst C z c
  · intro d hd
    exact formulaConstSymbolsN_formulaSubstConst_ C z c d hd
  · intro v hv
    rcases formulaFV_formulaSubstConst_sub C z c v hv.1 with hCv | hvz
    · exact hCv
    · exact (hv.2 hvz).elim
  · intro hNoEq
    exact formulaSubstConst_noEq C z c hNoEq

theorem interpolant_fix_one_fv {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (Γ₁ Δ₁ Γ₂ Δ₂ : List (FormulaN L)) (C : FormulaN L) (v : Nat)
    (hLeft : lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C]⟩)
    (hRight : lkBotProvable botP hBotArity ⟨[C] ++ Γ₂, Δ₂⟩)
    (hFreshLeft : ∀ F ∈ Γ₁ ++ Δ₁, v ∉ formulaFVN F) :
    ∃ C' : FormulaN L,
      lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C']⟩ ∧
      lkBotProvable botP hBotArity ⟨[C'] ++ Γ₂, Δ₂⟩ ∧
      formulaPredSymbolsN C' = formulaPredSymbolsN C ∧
      formulaConstSymbolsN C' = formulaConstSymbolsN C ∧
      (∀ w, formulaFVN C' w → formulaFVN C w ∧ w ≠ v) ∧
      (formulaNoEq C → formulaNoEq C') := by
  let C' := FormulaN.all v C
  have hFreshConclusion :
      ∀ F ∈
          (Sequent.mk Γ₁ (Δ₁ ++ [C'])).antecedent ++
            (Sequent.mk Γ₁ (Δ₁ ++ [C'])).succedent,
        v ∉ formulaFVN F := by
    intro F hF
    change F ∈ Γ₁ ++ (Δ₁ ++ [C']) at hF
    rcases List.mem_append.mp hF with hΓ | hΔC
    · exact hFreshLeft F (List.mem_append_left _ hΓ)
    · rcases List.mem_append.mp hΔC with hΔ | hC'
      · exact hFreshLeft F (List.mem_append_right _ hΔ)
      · have hFC' : F = C' := by simpa using hC'
        subst F
        intro hv
        exact hv.2 rfl
  have hLeft' : lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C']⟩ := by
    apply lkBot_onePremise
      (FOLKStep1.allRight v v C Γ₁ Δ₁ hFreshConclusion
        (isFreeForN_var_self C v))
    simpa [C', formulaSubstN_var_self] using hLeft
  have hRight' : lkBotProvable botP hBotArity ⟨[C'] ++ Γ₂, Δ₂⟩ := by
    apply lkBot_onePremise
      (FOLKStep1.allLeft (.var v) v C Γ₂ Δ₂
        (isFreeForN_var_self C v))
    simpa [C', formulaSubstN_var_self] using hRight
  refine ⟨C', hLeft', hRight', rfl, rfl, ?_, ?_⟩
  · intro w hw
    exact ⟨hw.1, hw.2⟩
  · exact id

theorem interpolant_fix_consts {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (Γ₁ Δ₁ Γ₂ Δ₂ : List (FormulaN L)) (C : FormulaN L) (cs : List L.constSymbols)
    (hLeft : lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C]⟩)
    (hRight : lkBotProvable botP hBotArity ⟨[C] ++ Γ₂, Δ₂⟩)
    (hNoConst : ∀ c ∈ cs, ∀ F ∈ Γ₁ ++ Δ₁, ¬ formulaConstSymbolsN F c) :
    ∃ C', lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C']⟩ ∧ lkBotProvable botP hBotArity ⟨[C'] ++ Γ₂, Δ₂⟩ ∧
      formulaPredSymbolsN C' = formulaPredSymbolsN C ∧
      (∀ d, formulaConstSymbolsN C' d → formulaConstSymbolsN C d ∧ d ∉ cs) ∧
      (∀ v, formulaFVN C' v → formulaFVN C v) ∧
      (formulaNoEq C → formulaNoEq C') := by
  induction cs generalizing C with
  | nil =>
    refine ⟨C, hLeft, hRight, rfl, ?_, ?_, ?_⟩
    · intro d hd
      exact ⟨hd, by simp⟩
    · intro v hv
      exact hv
    · exact id
  | cons c cs ih =>
    have hNoConstHead :
        ∀ F ∈ Γ₁ ++ Δ₁, ¬ formulaConstSymbolsN F c :=
      hNoConst c (by simp)
    have hNoConstTail :
        ∀ d ∈ cs, ∀ F ∈ Γ₁ ++ Δ₁, ¬ formulaConstSymbolsN F d := by
      intro d hd
      exact hNoConst d (List.mem_cons_of_mem c hd)
    obtain ⟨C₁, hLeft₁, hRight₁, hPred₁, hConst₁, hFV₁, hNoEq₁⟩ :=
      interpolant_fix_one_const Γ₁ Δ₁ Γ₂ Δ₂ C c
        hLeft hRight hNoConstHead
    obtain ⟨C₂, hLeft₂, hRight₂, hPred₂, hConst₂, hFV₂, hNoEq₂⟩ :=
      ih C₁ hLeft₁ hRight₁ hNoConstTail
    refine ⟨C₂, hLeft₂, hRight₂, hPred₂.trans hPred₁, ?_, ?_, ?_⟩
    · intro d hd
      obtain ⟨hC₁d, hdNotCs⟩ := hConst₂ d hd
      obtain ⟨hCd, hdNeC⟩ := hConst₁ d hC₁d
      refine ⟨hCd, ?_⟩
      intro hdMem
      rcases List.mem_cons.mp hdMem with hdc | hdcs
      · exact hdNeC hdc
      · exact hdNotCs hdcs
    · intro v hv
      exact hFV₁ v (hFV₂ v hv)
    · intro hNoEq
      exact hNoEq₂ (hNoEq₁ hNoEq)

theorem interpolant_fix_fvs {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (Γ₁ Δ₁ Γ₂ Δ₂ : List (FormulaN L)) (C : FormulaN L) (vs : List Nat)
    (hLeft : lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C]⟩)
    (hRight : lkBotProvable botP hBotArity ⟨[C] ++ Γ₂, Δ₂⟩)
    (hFresh : ∀ v ∈ vs, ∀ F ∈ Γ₁ ++ Δ₁, v ∉ formulaFVN F) :
    ∃ C', lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C']⟩ ∧ lkBotProvable botP hBotArity ⟨[C'] ++ Γ₂, Δ₂⟩ ∧
      formulaPredSymbolsN C' = formulaPredSymbolsN C ∧
      formulaConstSymbolsN C' = formulaConstSymbolsN C ∧
      (∀ w, formulaFVN C' w → formulaFVN C w ∧ w ∉ vs) ∧
      (formulaNoEq C → formulaNoEq C') := by
  induction vs generalizing C with
  | nil =>
    refine ⟨C, hLeft, hRight, rfl, rfl, ?_, ?_⟩
    · intro w hw
      exact ⟨hw, by simp⟩
    · exact id
  | cons v vs ih =>
    have hFreshHead :
        ∀ F ∈ Γ₁ ++ Δ₁, v ∉ formulaFVN F :=
      hFresh v (by simp)
    have hFreshTail :
        ∀ w ∈ vs, ∀ F ∈ Γ₁ ++ Δ₁, w ∉ formulaFVN F := by
      intro w hw
      exact hFresh w (List.mem_cons_of_mem v hw)
    obtain ⟨C₁, hLeft₁, hRight₁, hPred₁, hConst₁, hFV₁, hNoEq₁⟩ :=
      interpolant_fix_one_fv Γ₁ Δ₁ Γ₂ Δ₂ C v
        hLeft hRight hFreshHead
    obtain ⟨C₂, hLeft₂, hRight₂, hPred₂, hConst₂, hFV₂, hNoEq₂⟩ :=
      ih C₁ hLeft₁ hRight₁ hFreshTail
    refine
      ⟨C₂, hLeft₂, hRight₂, hPred₂.trans hPred₁,
        hConst₂.trans hConst₁, ?_, ?_⟩
    · intro w hw
      obtain ⟨hC₁w, hwNotVs⟩ := hFV₂ w hw
      obtain ⟨hCw, hwNeV⟩ := hFV₁ w hC₁w
      refine ⟨hCw, ?_⟩
      intro hwMem
      rcases List.mem_cons.mp hwMem with hwv | hwvs
      · exact hwNeV hwv
      · exact hwNotVs hwvs
    · intro hNoEq
      exact hNoEq₂ (hNoEq₁ hNoEq)

theorem interpolant_fix_one_const_right {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (Γ₁ Δ₁ Γ₂ Δ₂ : List (FormulaN L)) (C : FormulaN L) (c : L.constSymbols)
    (hLeft : lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C]⟩)
    (hRight : lkBotProvable botP hBotArity ⟨[C] ++ Γ₂, Δ₂⟩)
    (hNoConstRight : ∀ F ∈ Γ₂ ++ Δ₂, ¬ formulaConstSymbolsN F c) :
    ∃ C' : FormulaN L,
      lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C']⟩ ∧
      lkBotProvable botP hBotArity ⟨[C'] ++ Γ₂, Δ₂⟩ ∧
      formulaPredSymbolsN C' = formulaPredSymbolsN C ∧
      (∀ d, formulaConstSymbolsN C' d → formulaConstSymbolsN C d ∧ d ≠ c) ∧
      (∀ v, formulaFVN C' v → formulaFVN C v) ∧
      (formulaNoEq C → formulaNoEq C') := by
-- BEGIN PROOF
  have hNegLeft :
      lkBotProvable botP hBotArity ⟨Γ₂, Δ₂ ++ [.neg C]⟩ :=
    lkBot_onePremise (.negRight C Γ₂ Δ₂) hRight
  have hNegRight :
      lkBotProvable botP hBotArity ⟨[.neg C] ++ Γ₁, Δ₁⟩ :=
    lkBot_onePremise (.negLeft C Γ₁ Δ₁) hLeft
  obtain ⟨D, hDLeft, hDRight, hPred, hConst, hFV, hNoEq⟩ :=
    interpolant_fix_one_const Γ₂ Δ₂ Γ₁ Δ₁ (.neg C) c
      hNegLeft hNegRight hNoConstRight
  refine ⟨.neg D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lkBot_onePremise (.negRight D Γ₁ Δ₁) hDRight
  · exact lkBot_onePremise (.negLeft D Γ₂ Δ₂) hDLeft
  · simpa only [formulaPredSymbolsN] using hPred
  · intro d hd
    exact hConst d (by simpa only [formulaConstSymbolsN] using hd)
  · intro w hw
    exact hFV w (by simpa only [formulaFVN] using hw)
  · intro hC
    exact hNoEq (by simpa only [formulaNoEq] using hC)

theorem interpolant_fix_one_fv_right {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (Γ₁ Δ₁ Γ₂ Δ₂ : List (FormulaN L)) (C : FormulaN L) (v : Nat)
    (hLeft : lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C]⟩)
    (hRight : lkBotProvable botP hBotArity ⟨[C] ++ Γ₂, Δ₂⟩)
    (hFreshRight : ∀ F ∈ Γ₂ ++ Δ₂, v ∉ formulaFVN F) :
    ∃ C' : FormulaN L,
      lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C']⟩ ∧
      lkBotProvable botP hBotArity ⟨[C'] ++ Γ₂, Δ₂⟩ ∧
      formulaPredSymbolsN C' = formulaPredSymbolsN C ∧
      formulaConstSymbolsN C' = formulaConstSymbolsN C ∧
      (∀ w, formulaFVN C' w → formulaFVN C w ∧ w ≠ v) ∧
      (formulaNoEq C → formulaNoEq C') := by
-- BEGIN PROOF
  have hNegLeft :
      lkBotProvable botP hBotArity ⟨Γ₂, Δ₂ ++ [.neg C]⟩ :=
    lkBot_onePremise (.negRight C Γ₂ Δ₂) hRight
  have hNegRight :
      lkBotProvable botP hBotArity ⟨[.neg C] ++ Γ₁, Δ₁⟩ :=
    lkBot_onePremise (.negLeft C Γ₁ Δ₁) hLeft
  obtain ⟨D, hDLeft, hDRight, hPred, hConst, hFV, hNoEq⟩ :=
    interpolant_fix_one_fv Γ₂ Δ₂ Γ₁ Δ₁ (.neg C) v
      hNegLeft hNegRight hFreshRight
  refine ⟨.neg D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lkBot_onePremise (.negRight D Γ₁ Δ₁) hDRight
  · exact lkBot_onePremise (.negLeft D Γ₂ Δ₂) hDLeft
  · simpa only [formulaPredSymbolsN] using hPred
  · simpa only [formulaConstSymbolsN] using hConst
  · intro w hw
    exact hFV w (by simpa only [formulaFVN] using hw)
  · intro hC
    exact hNoEq (by simpa only [formulaNoEq] using hC)

theorem interpolant_fix_consts_right {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (Γ₁ Δ₁ Γ₂ Δ₂ : List (FormulaN L)) (C : FormulaN L) (cs : List L.constSymbols)
    (hLeft : lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C]⟩)
    (hRight : lkBotProvable botP hBotArity ⟨[C] ++ Γ₂, Δ₂⟩)
    (hNoConst : ∀ c ∈ cs, ∀ F ∈ Γ₂ ++ Δ₂, ¬ formulaConstSymbolsN F c) :
    ∃ C', lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C']⟩ ∧ lkBotProvable botP hBotArity ⟨[C'] ++ Γ₂, Δ₂⟩ ∧
      formulaPredSymbolsN C' = formulaPredSymbolsN C ∧
      (∀ d, formulaConstSymbolsN C' d → formulaConstSymbolsN C d ∧ d ∉ cs) ∧
      (∀ v, formulaFVN C' v → formulaFVN C v) ∧
      (formulaNoEq C → formulaNoEq C') := by
  induction cs generalizing C with
  | nil =>
      refine ⟨C, hLeft, hRight, rfl, ?_, ?_, ?_⟩
      · intro d hd
        exact ⟨hd, List.not_mem_nil⟩
      · intro v hv
        exact hv
      · exact id
  | cons c cs ih =>
      have hNoHead :
          ∀ F ∈ Γ₂ ++ Δ₂, ¬ formulaConstSymbolsN F c :=
        hNoConst c (List.Mem.head _)
      obtain ⟨C₁, hLeft₁, hRight₁, hPred₁, hConst₁, hFV₁, hNoEq₁⟩ :=
        interpolant_fix_one_const_right Γ₁ Δ₁ Γ₂ Δ₂ C c
          hLeft hRight hNoHead
      have hNoTail :
          ∀ d ∈ cs, ∀ F ∈ Γ₂ ++ Δ₂, ¬ formulaConstSymbolsN F d := by
        intro d hd
        exact hNoConst d (List.Mem.tail _ hd)
      obtain ⟨C₂, hLeft₂, hRight₂, hPred₂, hConst₂, hFV₂, hNoEq₂⟩ :=
        ih C₁ hLeft₁ hRight₁ hNoTail
      refine ⟨C₂, hLeft₂, hRight₂, hPred₂.trans hPred₁, ?_, ?_, ?_⟩
      · intro d hd
        rcases hConst₂ d hd with ⟨hd₁, hdTail⟩
        rcases hConst₁ d hd₁ with ⟨hdC, hdHead⟩
        refine ⟨hdC, ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨hdHead, hdTail⟩
      · intro v hv
        exact hFV₁ v (hFV₂ v hv)
      · intro hNoEq
        exact hNoEq₂ (hNoEq₁ hNoEq)

theorem interpolant_fix_fvs_right {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (Γ₁ Δ₁ Γ₂ Δ₂ : List (FormulaN L)) (C : FormulaN L) (vs : List Nat)
    (hLeft : lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C]⟩)
    (hRight : lkBotProvable botP hBotArity ⟨[C] ++ Γ₂, Δ₂⟩)
    (hFresh : ∀ v ∈ vs, ∀ F ∈ Γ₂ ++ Δ₂, v ∉ formulaFVN F) :
    ∃ C', lkBotProvable botP hBotArity ⟨Γ₁, Δ₁ ++ [C']⟩ ∧ lkBotProvable botP hBotArity ⟨[C'] ++ Γ₂, Δ₂⟩ ∧
      formulaPredSymbolsN C' = formulaPredSymbolsN C ∧
      formulaConstSymbolsN C' = formulaConstSymbolsN C ∧
      (∀ w, formulaFVN C' w → formulaFVN C w ∧ w ∉ vs) ∧
      (formulaNoEq C → formulaNoEq C') := by
  induction vs generalizing C with
  | nil =>
      refine ⟨C, hLeft, hRight, rfl, rfl, ?_, ?_⟩
      · intro w hw
        exact ⟨hw, List.not_mem_nil⟩
      · exact id
  | cons v vs ih =>
      have hFreshHead :
          ∀ F ∈ Γ₂ ++ Δ₂, v ∉ formulaFVN F :=
        hFresh v (List.Mem.head _)
      obtain ⟨C₁, hLeft₁, hRight₁, hPred₁, hConst₁, hFV₁, hNoEq₁⟩ :=
        interpolant_fix_one_fv_right Γ₁ Δ₁ Γ₂ Δ₂ C v
          hLeft hRight hFreshHead
      have hFreshTail :
          ∀ w ∈ vs, ∀ F ∈ Γ₂ ++ Δ₂, w ∉ formulaFVN F := by
        intro w hw
        exact hFresh w (List.Mem.tail _ hw)
      obtain ⟨C₂, hLeft₂, hRight₂, hPred₂, hConst₂, hFV₂, hNoEq₂⟩ :=
        ih C₁ hLeft₁ hRight₁ hFreshTail
      refine
        ⟨C₂, hLeft₂, hRight₂, hPred₂.trans hPred₁,
          hConst₂.trans hConst₁, ?_, ?_⟩
      · intro w hw
        rcases hFV₂ w hw with ⟨hw₁, hwTail⟩
        rcases hFV₁ w hw₁ with ⟨hwC, hwHead⟩
        refine ⟨hwC, ?_⟩
        simp only [List.mem_cons, not_or]
        exact ⟨hwHead, hwTail⟩
      · intro hNoEq
        exact hNoEq₂ (hNoEq₁ hNoEq)

-- ===================================================================
-- Monotonicity of ∀ over partition components
-- ===================================================================

theorem allMem_mono_gamma1 {L : Language} {g1 g1' d1 g2 d2 : List (FormulaN L)}
    (hsub : ∀ F, F ∈ g1' → F ∈ g1)
    {P : FormulaN L → Prop} (h : ∀ F ∈ g1 ++ d1 ++ g2 ++ d2, P F) :
    ∀ F ∈ g1' ++ d1 ++ g2 ++ d2, P F := by
-- BEGIN PROOF
  intro F hF; apply h; simp only [List.mem_append] at hF ⊢
  rcases hF with ((h1|h1)|h1)|h1
  · left; left; left; exact hsub F h1
  · left; left; right; exact h1
  · left; right; exact h1
  · right; exact h1

theorem allMem_mono_delta1 {L : Language} {g1 d1 d1' g2 d2 : List (FormulaN L)}
    (hsub : ∀ F, F ∈ d1' → F ∈ d1)
    {P : FormulaN L → Prop} (h : ∀ F ∈ g1 ++ d1 ++ g2 ++ d2, P F) :
    ∀ F ∈ g1 ++ d1' ++ g2 ++ d2, P F := by
-- BEGIN PROOF
  intro F hF; apply h; simp only [List.mem_append] at hF ⊢
  rcases hF with ((h1|h1)|h1)|h1
  · left; left; left; exact h1
  · left; left; right; exact hsub F h1
  · left; right; exact h1
  · right; exact h1

theorem allMem_mono_gamma2 {L : Language} {g1 d1 g2 g2' d2 : List (FormulaN L)}
    (hsub : ∀ F, F ∈ g2' → F ∈ g2)
    {P : FormulaN L → Prop} (h : ∀ F ∈ g1 ++ d1 ++ g2 ++ d2, P F) :
    ∀ F ∈ g1 ++ d1 ++ g2' ++ d2, P F := by
-- BEGIN PROOF
  intro F hF; apply h; simp only [List.mem_append] at hF ⊢
  rcases hF with ((h1|h1)|h1)|h1
  · left; left; left; exact h1
  · left; left; right; exact h1
  · left; right; exact hsub F h1
  · right; exact h1

theorem allMem_mono_delta2 {L : Language} {g1 d1 g2 d2 d2' : List (FormulaN L)}
    (hsub : ∀ F, F ∈ d2' → F ∈ d2)
    {P : FormulaN L → Prop} (h : ∀ F ∈ g1 ++ d1 ++ g2 ++ d2, P F) :
    ∀ F ∈ g1 ++ d1 ++ g2 ++ d2', P F := by
-- BEGIN PROOF
  intro F hF; apply h; simp only [List.mem_append] at hF ⊢
  rcases hF with ((h1|h1)|h1)|h1
  · left; left; left; exact h1
  · left; left; right; exact h1
  · left; right; exact h1
  · right; exact hsub F h1

-- ===================================================================
-- formula_empty_pred_no_base
-- ===================================================================

theorem formula_empty_pred_no_base {L : Language}
    (hEmpty : ¬Nonempty L.predSymbols)
    (F : FormulaN L)
    (hNoEq : formulaNoEq F) : False := by
-- BEGIN PROOF
  induction F with
  | predN P _ => exact hEmpty ⟨P⟩
  | eq_ _ _ => exact hNoEq
  | neg A ih => exact ih hNoEq
  | conj A B ihA _ => exact ihA hNoEq.1
  | disj A B ihA _ => exact ihA hNoEq.1
  | impl A B ihA _ => exact ihA hNoEq.1
  | all _ A ih => exact ih hNoEq
  | ex _ A ih => exact ih hNoEq

-- ===================================================================
-- botFormula_lkBotProvable_or_lkBotRefutable
-- ===================================================================

theorem botFormula_lkBotProvable_or_lkBotRefutable {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    (C : FormulaN L)
    (hOnlyBot : ∀ P : L.predSymbols, formulaPredSymbolsN C P → P = botP)
    (hNoEq : formulaNoEq C) :
    lkBotProvable botP hBotArity { antecedent := ([] : List (FormulaN L)), succedent := [C] } ∨
    lkBotProvable botP hBotArity { antecedent := [C], succedent := ([] : List (FormulaN L)) } := by
-- BEGIN PROOF
  induction C with
  | predN P ts =>
    have hP : P = botP := hOnlyBot P rfl
    subst P
    have hFormula : FormulaN.predN botP ts = botFormula botP hBotArity := by
      simp only [botFormula, FormulaN.predN.injEq, heq_eq_eq, true_and]
      funext i
      exact Fin.elim0 (hBotArity ▸ i)
    right
    rw [hFormula]
    exact ⟨.axiom_ ⟨[botFormula botP hBotArity], []⟩
      (Or.inr ⟨rfl, rfl⟩)⟩
  | eq_ _ _ _ => exact hNoEq.elim
  | neg A ih =>
    rcases ih (fun P hP => hOnlyBot P hP) hNoEq with hA | hA
    · right
      exact lkBot_onePremise (.negLeft A [] []) hA
    · left
      exact lkBot_onePremise (.negRight A [] []) hA
  | conj A B ihA ihB =>
    rcases ihA (fun P hP => hOnlyBot P (Or.inl hP)) hNoEq.1 with hA | hA
    · rcases ihB (fun P hP => hOnlyBot P (Or.inr hP)) hNoEq.2 with hB | hB
      · left
        exact lkBot_twoPremise (.andRight A B [] []) hA hB
      · right
        exact lkBot_onePremise (.andLeftR A B [] []) hB
    · right
      exact lkBot_onePremise (.andLeftL A B [] []) hA
  | disj A B ihA ihB =>
    rcases ihA (fun P hP => hOnlyBot P (Or.inl hP)) hNoEq.1 with hA | hA
    · left
      exact lkBot_onePremise (.orRightL A B [] []) hA
    · rcases ihB (fun P hP => hOnlyBot P (Or.inr hP)) hNoEq.2 with hB | hB
      · left
        exact lkBot_onePremise (.orRightR A B [] []) hB
      · right
        exact lkBot_twoPremise (.orLeft A B [] []) hA hB
  | impl A B ihA ihB =>
    rcases ihA (fun P hP => hOnlyBot P (Or.inl hP)) hNoEq.1 with hA | hA
    · rcases ihB (fun P hP => hOnlyBot P (Or.inr hP)) hNoEq.2 with hB | hB
      · left
        have hPrem := lkBot_onePremise (.weakenLeft A [] [B]) hB
        exact lkBot_onePremise (.implRight A B [] []) hPrem
      · right
        exact lkBot_twoPremise (.implLeft A B [] [] [] []) hA hB
    · left
      have hPrem := lkBot_onePremise (.weakenRight B [A] []) hA
      exact lkBot_onePremise (.implRight A B [] []) hPrem
  | all x A ih =>
    rcases ih (fun P hP => hOnlyBot P hP) hNoEq with hA | hA
    · left
      have hfresh :
          ∀ F ∈ (Sequent.mk [] ([] ++ [FormulaN.all x A])).antecedent ++
              (Sequent.mk [] ([] ++ [FormulaN.all x A])).succedent,
            x ∉ formulaFVN F := by
        intro F hF
        simp only [List.nil_append, List.mem_singleton] at hF
        subst F
        rintro ⟨_, hx⟩
        exact hx rfl
      have hPrem :
          lkBotProvable botP hBotArity
            ⟨[], [formulaSubstN A (.var x) x]⟩ := by
        simpa only [formulaSubstN_var_self] using hA
      exact lkBot_onePremise
        (.allRight x x A [] [] hfresh (isFreeForN_var_self A x)) hPrem
    · right
      have hPrem :
          lkBotProvable botP hBotArity
            ⟨[formulaSubstN A (.var x) x], []⟩ := by
        simpa only [formulaSubstN_var_self] using hA
      exact lkBot_onePremise
        (.allLeft (.var x) x A [] [] (isFreeForN_var_self A x)) hPrem
  | ex x A ih =>
    rcases ih (fun P hP => hOnlyBot P hP) hNoEq with hA | hA
    · left
      have hPrem :
          lkBotProvable botP hBotArity
            ⟨[], [formulaSubstN A (.var x) x]⟩ := by
        simpa only [formulaSubstN_var_self] using hA
      exact lkBot_onePremise
        (.exRight (.var x) x A [] [] (isFreeForN_var_self A x)) hPrem
    · right
      have hfresh :
          ∀ F ∈ (Sequent.mk (FormulaN.ex x A :: []) []).antecedent ++
              (Sequent.mk (FormulaN.ex x A :: []) []).succedent,
            x ∉ formulaFVN F := by
        intro F hF
        simp only [List.append_nil, List.mem_singleton] at hF
        subst F
        rintro ⟨_, hx⟩
        exact hx rfl
      have hPrem :
          lkBotProvable botP hBotArity
            ⟨[formulaSubstN A (.var x) x], []⟩ := by
        simpa only [formulaSubstN_var_self] using hA
      exact lkBot_onePremise
        (.exLeft x x A [] [] hfresh (isFreeForN_var_self A x)) hPrem

-- ===================================================================
-- Helper: interpolation for well-formed LKBot proof trees (induction)
-- ===================================================================

theorem isInterpolant_transport {L : Language}
    {botP : L.predSymbols} {hBotArity : L.predArity botP = 0}
    {s r : Sequent L} {p : SequentPartition s} {q : SequentPartition r}
    {C : FormulaN L}
    (hI : IsInterpolant botP hBotArity q C)
    (hLeft :
      lkBotProvable botP hBotArity
          ⟨q.gamma1, q.delta1 ++ [C]⟩ →
        lkBotProvable botP hBotArity
          ⟨p.gamma1, p.delta1 ++ [C]⟩)
    (hRight :
      lkBotProvable botP hBotArity
          ⟨[C] ++ q.gamma2, q.delta2⟩ →
        lkBotProvable botP hBotArity
          ⟨[C] ++ p.gamma2, p.delta2⟩)
    (hPred1 :
      listFormulaPredSymbols (q.gamma1 ++ q.delta1) ⊆
        listFormulaPredSymbols (p.gamma1 ++ p.delta1))
    (hPred2 :
      listFormulaPredSymbols (q.gamma2 ++ q.delta2) ⊆
        listFormulaPredSymbols (p.gamma2 ++ p.delta2))
    (hConst1 :
      listFormulaConstSymbols (q.gamma1 ++ q.delta1) ⊆
        listFormulaConstSymbols (p.gamma1 ++ p.delta1))
    (hConst2 :
      listFormulaConstSymbols (q.gamma2 ++ q.delta2) ⊆
        listFormulaConstSymbols (p.gamma2 ++ p.delta2))
    (hFV1 :
      listFormulaFV (q.gamma1 ++ q.delta1) ⊆
        listFormulaFV (p.gamma1 ++ p.delta1))
    (hFV2 :
      listFormulaFV (q.gamma2 ++ q.delta2) ⊆
        listFormulaFV (p.gamma2 ++ p.delta2))
    (hNoEq :
      (∀ A ∈ p.gamma1 ++ p.delta1 ++ p.gamma2 ++ p.delta2, formulaNoEq A) →
      ∀ A ∈ q.gamma1 ++ q.delta1 ++ q.gamma2 ++ q.delta2, formulaNoEq A) :
    IsInterpolant botP hBotArity p C := by
  refine
    { left_provable := hLeft hI.left_provable
      right_provable := hRight hI.right_provable
      pred_common := ?_
      const_common := ?_
      fv_common := ?_
      no_eq := ?_ }
  · intro P hP hne
    exact ⟨hPred1 _ (hI.pred_common P hP hne).1,
      hPred2 _ (hI.pred_common P hP hne).2⟩
  · intro c hc
    exact ⟨hConst1 _ (hI.const_common c hc).1,
      hConst2 _ (hI.const_common c hc).2⟩
  · intro v hv
    exact ⟨hFV1 _ (hI.fv_common v hv).1,
      hFV2 _ (hI.fv_common v hv).2⟩
  · exact fun h => hI.no_eq (hNoEq h)

theorem allNoEq_mono {L : Language}
    {s r : Sequent L} {p : SequentPartition s} {q : SequentPartition r}
    (h₁ : ∀ F, F ∈ q.gamma1 ++ q.delta1 → F ∈ p.gamma1 ++ p.delta1)
    (h₂ : ∀ F, F ∈ q.gamma2 ++ q.delta2 → F ∈ p.gamma2 ++ p.delta2) :
    (∀ A ∈ p.gamma1 ++ p.delta1 ++ p.gamma2 ++ p.delta2, formulaNoEq A) →
      ∀ A ∈ q.gamma1 ++ q.delta1 ++ q.gamma2 ++ q.delta2, formulaNoEq A := by
  intro h A hA
  apply h A
  rcases List.mem_append.mp hA with hA | hA
  · rcases List.mem_append.mp hA with hA | hA
    · rcases List.mem_append.mp (h₁ A hA) with hA | hA
      · exact List.mem_append.mpr (Or.inl <|
          List.mem_append.mpr (Or.inl <| List.mem_append.mpr (Or.inl hA)))
      · exact List.mem_append.mpr (Or.inl <|
          List.mem_append.mpr (Or.inl <| List.mem_append.mpr (Or.inr hA)))
    · rcases List.mem_append.mp
          (h₂ A (List.mem_append.mpr (Or.inl hA))) with hA | hA
      · exact List.mem_append.mpr (Or.inl <|
          List.mem_append.mpr (Or.inr hA))
      · exact List.mem_append.mpr (Or.inr hA)
  · rcases List.mem_append.mp
        (h₂ A (List.mem_append.mpr (Or.inr hA))) with hA | hA
    · exact List.mem_append.mpr (Or.inl <|
        List.mem_append.mpr (Or.inr hA))
    · exact List.mem_append.mpr (Or.inr hA)

theorem allNoEq_rel {L : Language}
    {s r : Sequent L} {p : SequentPartition s} {q : SequentPartition r}
    (h₁ : ∀ F, F ∈ q.gamma1 ++ q.delta1 →
      ∃ G ∈ p.gamma1 ++ p.delta1, formulaNoEq G → formulaNoEq F)
    (h₂ : ∀ F, F ∈ q.gamma2 ++ q.delta2 →
      ∃ G ∈ p.gamma2 ++ p.delta2, formulaNoEq G → formulaNoEq F) :
    (∀ A ∈ p.gamma1 ++ p.delta1 ++ p.gamma2 ++ p.delta2, formulaNoEq A) →
      ∀ A ∈ q.gamma1 ++ q.delta1 ++ q.gamma2 ++ q.delta2, formulaNoEq A := by
  intro h A hA
  rcases List.mem_append.mp hA with hA | hA
  · rcases List.mem_append.mp hA with hA | hA
    · obtain ⟨G, hG, hno⟩ := h₁ A hA
      apply hno
      apply h G
      exact List.mem_append.mpr (Or.inl <|
        List.mem_append.mpr (Or.inl hG))
    · obtain ⟨G, hG, hno⟩ :=
        h₂ A (List.mem_append.mpr (Or.inl hA))
      apply hno
      apply h G
      rcases List.mem_append.mp hG with hG | hG
      · exact List.mem_append.mpr (Or.inl <|
          List.mem_append.mpr (Or.inr hG))
      · exact List.mem_append.mpr (Or.inr hG)
  · obtain ⟨G, hG, hno⟩ :=
      h₂ A (List.mem_append.mpr (Or.inr hA))
    apply hno
    apply h G
    rcases List.mem_append.mp hG with hG | hG
    · exact List.mem_append.mpr (Or.inl <|
        List.mem_append.mpr (Or.inr hG))
    · exact List.mem_append.mpr (Or.inr hG)

end LCS.CutElim.Interpolation
end

