import LCS.Item
import LCS.Util
import LCS.CutElim.LK
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.CutElim.LKe.Equivalence
import LCS.CutElim.Interpolation.LKBot
import LCS.CutElim.Interpolation.ProofSubstitution.Basic
import Attach
import LCS.CutElim.Interpolation.FreshVariables.ProofsStamp

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

-- ===================================================================
-- VarFresh infrastructure
-- ===================================================================
theorem foldl_max_init_le (init : Nat) (l : List Nat) :
    init ≤ l.foldl Nat.max init := by
-- BEGIN PROOF
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons hd t ih => exact Nat.le_trans (Nat.le_max_left init hd) (ih _)

theorem foldl_max_mem_le (l : List Nat) (init : Nat) (x : Nat) (hx : x ∈ l) :
    x ≤ l.foldl Nat.max init := by
-- BEGIN PROOF
  induction l generalizing init with
  | nil => simp at hx
  | cons hd t ih =>
    rcases List.mem_cons.mp hx with rfl | ht
    · exact Nat.le_trans (Nat.le_max_right init x) (foldl_max_init_le _ _)
    · exact ih (Nat.max init hd) ht

def termMaxVar {L : Language} : Term L → Nat
  | .var i => i
  | .const _ => 0
  | .func _ ts => (List.ofFn fun i => termMaxVar (ts i)).foldl Nat.max 0

theorem termFV_bounded {L : Language} (t : Term L) (v : Nat) (hv : termFV t v) :
    v ≤ termMaxVar t := by
-- BEGIN PROOF
  induction t with
  | var i => change v = i at hv; subst hv; exact Nat.le_refl _
  | const _ => change False at hv; exact absurd hv id
  | func _ ts ih =>
    change ∃ i, termFV (ts i) v at hv; obtain ⟨i, hi⟩ := hv
    exact Nat.le_trans (ih i hi) (foldl_max_mem_le _ 0 _ (List.mem_ofFn.mpr ⟨i, rfl⟩))

theorem termFV_gt_maxVar {L : Language} (t : Term L) (v : Nat) (hv : v > termMaxVar t) :
    v ∉ termFV t :=
-- BEGIN PROOF
  fun h => Nat.not_lt.mpr (termFV_bounded t v h) hv

-- ===================================================================
-- Max var in tree
-- ===================================================================
def formulaAllMaxVar {L : Language} : FormulaN L → Nat
  | .predN _ ts => (List.ofFn fun i => termMaxVar (ts i)).foldl Nat.max 0
  | .eq_ _ t1 t2 => Nat.max (termMaxVar t1) (termMaxVar t2)
  | .conj A B => Nat.max (formulaAllMaxVar A) (formulaAllMaxVar B)
  | .disj A B => Nat.max (formulaAllMaxVar A) (formulaAllMaxVar B)
  | .impl A B => Nat.max (formulaAllMaxVar A) (formulaAllMaxVar B)
  | .neg A => formulaAllMaxVar A
  | .all x A => Nat.max x (formulaAllMaxVar A)
  | .ex x A => Nat.max x (formulaAllMaxVar A)

theorem formulaAllMaxVar_gt_no_fv {L : Language} (A : FormulaN L) (v : Nat)
    (hv : v > formulaAllMaxVar A) : v ∉ formulaFVN A := by
-- BEGIN PROOF
  induction A with
  | predN _ ts =>
    intro h; obtain ⟨i, hi⟩ := h
    exact Nat.not_lt.mpr (termFV_bounded (ts i) v hi)
      (Nat.lt_of_le_of_lt (foldl_max_mem_le _ 0 _ (List.mem_ofFn.mpr ⟨i, rfl⟩)) hv)
  | eq_ _ t1 t2 =>
    intro h; rcases h with h1 | h2
    · exact Nat.not_lt.mpr (termFV_bounded t1 v h1)
        (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv)
    · exact Nat.not_lt.mpr (termFV_bounded t2 v h2)
        (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv)
  | conj A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | disj A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | impl A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | neg A ih => exact ih hv
  | all x A ih =>
    intro ⟨hA, _⟩; exact ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hA
  | ex x A ih =>
    intro ⟨hA, _⟩; exact ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hA

theorem formulaAllMaxVar_gt_no_bv {L : Language} (A : FormulaN L) (v : Nat)
    (hv : v > formulaAllMaxVar A) : v ∉ formulaBVN A := by
-- BEGIN PROOF
  induction A with
  | predN _ _ => intro h; exact h
  | eq_ _ _ => intro h; exact h
  | conj A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | disj A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | impl A B ihA ihB =>
    intro h; rcases h with hA | hB
    · exact ihA (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hv) hA
    · exact ihB (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hB
  | neg A ih => exact ih hv
  | all x A ih =>
    intro h; rcases h with hA | hx
    · exact ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hA
    · subst hx; exact Nat.not_lt.mpr (Nat.le_max_left _ _) hv
  | ex x A ih =>
    intro h; rcases h with hA | hx
    · exact ih (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hv) hA
    · subst hx; exact Nat.not_lt.mpr (Nat.le_max_left _ _) hv

def listFormulaAllMaxVar {L : Language} (fs : List (FormulaN L)) : Nat :=
  (fs.map formulaAllMaxVar).foldl Nat.max 0

def sequentAllMaxVar {L : Language} (s : Sequent L) : Nat :=
  Nat.max (listFormulaAllMaxVar s.antecedent) (listFormulaAllMaxVar s.succedent)

-- ===================================================================
-- Term symbol lists and sequential substitution
-- ===================================================================

@[blueprint "chap6__definition_6_5_1"]
def FormulaN.allList {L : Language} (vars : List Nat) (F : FormulaN L) : FormulaN L :=
  vars.foldr FormulaN.all F

end LCS.CutElim.Interpolation
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

end LCS.CutElim.Interpolation
end
