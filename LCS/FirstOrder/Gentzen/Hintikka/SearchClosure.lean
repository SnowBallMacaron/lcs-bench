import LCS.Item
import LCS.Util
import LCS.FirstOrder.Gentzen
import LCS.FirstOrder.Gentzen.SignedFormulae
import LCS.FirstOrder.Gentzen.Hintikka.Model

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): SearchState
record from the pre-refactor pipeline, used only by Thm 5.5.1's
abstract-existence scaffolding (`goedelExtendedCompletenessG`) and
its downstream Thm 5.6.1 callers. Uses `SignedFormula`-keyed usage
records and a finite `availVars : Nat → Nat` stream — neither is
textbook-faithful; the faithful Def 5.4.9 state lives in
`LCS.FirstOrder.Gentzen.Search.NoFunction.SearchState` with `FormulaN`
keys and an implicit countably-infinite `availNext : Nat` stream.
Remove together with the unfaithful Thm 5.5.1 main and its
scaffolding chain. -/
structure SearchState (L : Language) where
  /-- TERM0 list: pairs of activated terms and their usage records -/
  termRecords : List (Term L × List (SignedFormula L))
  /-- AVAIL0 stream: maps indices to fresh variable numbers -/
  availVars : Nat → Nat
  /-- Current index into the AVAIL0 stream -/
  availIdx : Nat

end LCS.FirstOrder.Gentzen.Hintikka
end

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables
namespace SearchState

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): The set of
terms `{u_i}` extracted from the legacy `termRecords`. Faithful
counterpart in new pipeline is `SearchState.tTERM0` in
`LCS.FirstOrder.Gentzen.Search.NoFunction`. Used only by unfaithful
Thm 5.5.1 scaffolding. -/
def termSet {L : Language} (st : SearchState L) : Set (Term L) :=
  fun t => ∃ forms, (t, forms) ∈ st.termRecords

end SearchState
end LCS.FirstOrder.Gentzen.Hintikka
end

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables
namespace SearchState

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): Initialize
the legacy SearchState record. Doesn't collect constants (only FV),
uses `Term.var 0` as y₀ without checking freshness, and produces a
truncated `availVars` stream keyed by `startIdx`. Faithful counterpart
is `SearchState.init` in `LCS.FirstOrder.Gentzen.Search.NoFunction`.
Used only by unfaithful Thm 5.5.1 scaffolding. -/
def init {L : Language} (seq : Sequent L) : SearchState L :=
  -- Collect variable terms from free variables in all formulae
  let fvIndices := (seq.antecedent ++ seq.succedent).flatMap formulaFreeVarIndices
  let fvTerms := fvIndices.eraseDups.map Term.var
  -- If no terms found, use a single fresh variable y0
  let initialTerms : List (Term L) :=
    if fvTerms.isEmpty then [Term.var 0] else fvTerms
  let records := initialTerms.map (fun t => (t, ([] : List (SignedFormula L))))
  -- AVAIL0 starts at a fresh variable index beyond all used variables
  let startIdx := initialTerms.length
  { termRecords := records
  , availVars := fun n => startIdx + n
  , availIdx := 0 }

/-- Definition 5.5.1 (normalized companion): A sequent is a finished
leaf with respect to a (Hintikka-layer) search state `st` iff it is
an axiom, OR every antecedent formula A is atomic or has been used
with every term in TERM0 (witnessed by `SignedFormula.trueF A`
appearing in the usage list for every record), AND symmetrically for
succedent formulae B via `SignedFormula.falseF B`.

This is the normalized-pipeline parallel of
`LCS.FirstOrder.Completeness.SearchState.isFinishedLeaf` (which is
defined over the compatibility `Completeness.SearchState`). The
textbook "finished leaf" definition (Def 5.5.1) is the same; the
two layers only differ on how the usage records are keyed (SignedFormula
here vs FormulaN there). -/
def isFinishedLeaf {L : Language} (st : SearchState L)
    (seq : Sequent L) : Prop :=
  isAxiom seq ∨
  ((∀ A ∈ seq.antecedent,
    A.isAtomic ∨
    (∀ rec ∈ st.termRecords, SignedFormula.trueF A ∈ rec.2)) ∧
   (∀ B ∈ seq.succedent,
    B.isAtomic ∨
    (∀ rec ∈ st.termRecords, SignedFormula.falseF B ∈ rec.2)))

end SearchState
end LCS.FirstOrder.Gentzen.Hintikka
end

section
namespace LCS.FirstOrder.Gentzen.Hintikka
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.SemanticsN.Substitution
open LCS.FirstOrder.Gentzen
open LCS.FirstOrder.Gentzen.SignedFormulae
open LCS.FirstOrder.SyntaxN.Variables

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): Per-formula
antecedent decomposition helper for the pre-refactor `searchClosureStep`
pipeline. Textbook Def 5.4.9 expresses the same case analysis via the
grow-left / grow-right procedures, already formalized faithfully in
`LCS.FirstOrder.Gentzen.Search.NoFunction` (`growLeftAtLeaf` and friends).
Used only by unfaithful Thm 5.5.1 scaffolding. -/
def decomposeAntFormula {L : Language} (A : FormulaN L) (t_c t_d : Term L) :
    List (FormulaN L) × List (FormulaN L) :=
  match A with
  | .conj X Y => ([X, Y], [])
  | .disj _ _ => ([], [])  -- type-B: requires branching, not decomposed
  | .impl _ _ => ([], [])  -- type-B: requires branching, not decomposed
  | .neg X => ([], [X])
  | .all x B => ([formulaSubstN B t_c x], [])
  | .ex x B => ([formulaSubstN B t_d x], [])
  | .predN _ _ => ([], [])
  | .eq_ _ _ _ => ([], [])

-- ===================================================================
-- Normalized decomposition: decomposeSuccFormula
-- ===================================================================

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): Mirror of
`decomposeAntFormula` for the succedent. Superseded by `growRightAtLeaf`
and friends in `LCS.FirstOrder.Gentzen.Search.NoFunction`. -/
def decomposeSuccFormula {L : Language} (B : FormulaN L) (t_c t_d : Term L) :
    List (FormulaN L) × List (FormulaN L) :=
  match B with
  | .conj _ _ => ([], [])  -- type-B: requires branching, not decomposed
  | .disj X Y => ([], [X, Y])
  | .impl X Y => ([X], [Y])
  | .neg X => ([X], [])
  | .ex x A => ([], [formulaSubstN A t_c x])
  | .all x A => ([], [formulaSubstN A t_d x])
  | .predN _ _ => ([], [])
  | .eq_ _ _ _ => ([], [])

-- ===================================================================
-- Normalized collect helpers
-- ===================================================================

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): flatMap over
`decomposeAntFormula`'s antecedent output. Used only by unfaithful
Thm 5.5.1 scaffolding. -/
def collectDecompAnt {L : Language} (formulas : List (FormulaN L))
    (t_c t_d : Term L) : List (FormulaN L) :=
  formulas.flatMap (fun A => (decomposeAntFormula A t_c t_d).1)

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): flatMap over
`decomposeAntFormula`'s succedent output. -/
def collectDecompAntSucc {L : Language} (formulas : List (FormulaN L))
    (t_c t_d : Term L) : List (FormulaN L) :=
  formulas.flatMap (fun A => (decomposeAntFormula A t_c t_d).2)

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): flatMap over
`decomposeSuccFormula`'s antecedent output. -/
def collectDecompSuccAnt {L : Language} (formulas : List (FormulaN L))
    (t_c t_d : Term L) : List (FormulaN L) :=
  formulas.flatMap (fun B => (decomposeSuccFormula B t_c t_d).1)

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): flatMap over
`decomposeSuccFormula`'s succedent output. -/
def collectDecompSucc {L : Language} (formulas : List (FormulaN L))
    (t_c t_d : Term L) : List (FormulaN L) :=
  formulas.flatMap (fun B => (decomposeSuccFormula B t_c t_d).2)

-- ===================================================================
-- Normalized search closure step
-- ===================================================================

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): single-term
closure step from the pre-refactor pipeline. Concatenates decomposed
formulas to the sequent. Superseded by the grow-*TreeInv family +
`extendAllNonaxiomLeaves` in `LCS.FirstOrder.Gentzen.Search.NoFunction`,
which produce actual proof-tree nodes indexed by sequent rather than
flat sequent concatenations. -/
def searchClosureStep1 {L : Language} (prev : Sequent L)
    (t_c : Term L) (t_d : Term L) : Sequent L :=
  { antecedent := prev.antecedent
      ++ collectDecompAnt prev.antecedent t_c t_d
      ++ collectDecompSuccAnt prev.succedent t_c t_d
  , succedent := prev.succedent
      ++ collectDecompAntSucc prev.antecedent t_c t_d
      ++ collectDecompSucc prev.succedent t_c t_d }

/-- Theorem 5.5.1 (companion, UNFAITHFUL — TO REMOVE): many-term
version of `searchClosureStep1`. Same superseded status. -/
def searchClosureStep {L : Language} (prev : Sequent L)
    (t_cs : List (Term L)) (t_d : Term L) : Sequent L :=
  t_cs.foldl (fun acc t_c => searchClosureStep1 acc t_c t_d) prev

-- ===================================================================
-- Normalized search closure iteration
-- ===================================================================

/-- The normalized search closure: iterate searchClosureStep n times
from the initial normalized sequent. At step n, type-C formulas are
instantiated with ALL terms Countable.enumerate 0, ...,
Countable.enumerate n (ensuring every term eventually gets used for
every type-C formula). Type-D formulas get Term.var (freshBase + n) as
a fresh witness. -/
noncomputable def searchClosure {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) : Nat → Sequent L
  | 0 => seq
  | n + 1 =>
    let prev := searchClosure seq freshBase n
    let terms := (List.range (n + 1)).map Countable.enumerate
    searchClosureStep prev terms (Term.var (freshBase + n))

-- ===================================================================
-- Normalized monotonicity lemmas
-- ===================================================================

/-- searchClosureStep1 preserves antecedent membership. -/
theorem searchClosureStep1_ant_mono {L : Language}
    (prev : Sequent L) (t_c t_d : Term L) (A : FormulaN L) :
    A ∈ prev.antecedent → A ∈ (searchClosureStep1 prev t_c t_d).antecedent := by
-- BEGIN PROOF
  intro hA; simp only [searchClosureStep1]
  exact List.mem_append_left _ (List.mem_append_left _ hA)

/-- searchClosureStep1 preserves succedent membership. -/
theorem searchClosureStep1_succ_mono {L : Language}
    (prev : Sequent L) (t_c t_d : Term L) (B : FormulaN L) :
    B ∈ prev.succedent → B ∈ (searchClosureStep1 prev t_c t_d).succedent := by
-- BEGIN PROOF
  intro hB; simp only [searchClosureStep1]
  exact List.mem_append_left _ (List.mem_append_left _ hB)

/-- searchClosureStep (foldl) preserves antecedent membership. -/
theorem searchClosureStep_ant_mono {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L) (A : FormulaN L) :
    A ∈ prev.antecedent → A ∈ (searchClosureStep prev terms t_d).antecedent := by
-- BEGIN PROOF
  intro hA
  simp only [searchClosureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl]; exact hA
  | cons t ts ih =>
    simp [List.foldl]
    exact ih (searchClosureStep1 prev t t_d) (searchClosureStep1_ant_mono prev t t_d A hA)

/-- searchClosureStep (foldl) preserves succedent membership. -/
theorem searchClosureStep_succ_mono {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L) (B : FormulaN L) :
    B ∈ prev.succedent → B ∈ (searchClosureStep prev terms t_d).succedent := by
-- BEGIN PROOF
  intro hB
  simp only [searchClosureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl]; exact hB
  | cons t ts ih =>
    simp [List.foldl]
    exact ih (searchClosureStep1 prev t t_d) (searchClosureStep1_succ_mono prev t t_d B hB)


-- ===================================================================
-- Normalized decomposition membership helpers
-- ===================================================================

/-- If A is in a list, then (decomposeAntFormula A t_c t_d).1 contributes
to collectDecompAnt. -/
theorem mem_collectDecompAnt {L : Language}
    {formulas : List (FormulaN L)} {A : FormulaN L} {t_c t_d : Term L}
    (hA : A ∈ formulas) :
    ∀ X ∈ (decomposeAntFormula A t_c t_d).1, X ∈ collectDecompAnt formulas t_c t_d := by
-- BEGIN PROOF
  intro X hX
  simp only [collectDecompAnt, List.mem_flatMap]
  exact ⟨A, hA, hX⟩

theorem mem_collectDecompAntSucc {L : Language}
    {formulas : List (FormulaN L)} {A : FormulaN L} {t_c t_d : Term L}
    (hA : A ∈ formulas) :
    ∀ X ∈ (decomposeAntFormula A t_c t_d).2, X ∈ collectDecompAntSucc formulas t_c t_d := by
-- BEGIN PROOF
  intro X hX
  simp only [collectDecompAntSucc, List.mem_flatMap]
  exact ⟨A, hA, hX⟩

theorem mem_collectDecompSuccAnt {L : Language}
    {formulas : List (FormulaN L)} {B : FormulaN L} {t_c t_d : Term L}
    (hB : B ∈ formulas) :
    ∀ X ∈ (decomposeSuccFormula B t_c t_d).1, X ∈ collectDecompSuccAnt formulas t_c t_d := by
-- BEGIN PROOF
  intro X hX
  simp only [collectDecompSuccAnt, List.mem_flatMap]
  exact ⟨B, hB, hX⟩

theorem mem_collectDecompSucc {L : Language}
    {formulas : List (FormulaN L)} {B : FormulaN L} {t_c t_d : Term L}
    (hB : B ∈ formulas) :
    ∀ X ∈ (decomposeSuccFormula B t_c t_d).2, X ∈ collectDecompSucc formulas t_c t_d := by
-- BEGIN PROOF
  intro X hX
  simp only [collectDecompSucc, List.mem_flatMap]
  exact ⟨B, hB, hX⟩

-- ===================================================================
-- Normalized search closure decomposition lemmas
-- ===================================================================

/-- If A is in the antecedent of prev and t_c is in the terms list,
then the antecedent decomposition of A with t_c is in the result of
searchClosureStep. -/
theorem searchClosureStep_decompAnt {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (A : FormulaN L) (t_c : Term L)
    (hA : A ∈ prev.antecedent) (ht : t_c ∈ terms) :
    ∀ X ∈ (decomposeAntFormula A t_c t_d).1,
      X ∈ (searchClosureStep prev terms t_d).antecedent := by
-- BEGIN PROOF
  intro X hX
  simp only [searchClosureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl] at ht
  | cons hd tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp ht with rfl | htl
    · have hX1 : X ∈ (searchClosureStep1 prev t_c t_d).antecedent := by
        simp only [searchClosureStep1]
        apply List.mem_append_left
        apply List.mem_append_right
        exact mem_collectDecompAnt hA X hX
      exact searchClosureStep_ant_mono _ tl t_d X hX1
    · have hA' : A ∈ (searchClosureStep1 prev hd t_d).antecedent :=
        searchClosureStep1_ant_mono prev hd t_d A hA
      exact ih (searchClosureStep1 prev hd t_d) hA' htl

/-- Same for succedent decomposition. -/
theorem searchClosureStep_decompSucc {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (B : FormulaN L) (t_c : Term L)
    (hB : B ∈ prev.succedent) (ht : t_c ∈ terms) :
    ∀ X ∈ (decomposeSuccFormula B t_c t_d).2,
      X ∈ (searchClosureStep prev terms t_d).succedent := by
-- BEGIN PROOF
  intro X hX
  simp only [searchClosureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl] at ht
  | cons hd tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp ht with rfl | htl
    · have hX1 : X ∈ (searchClosureStep1 prev t_c t_d).succedent := by
        simp only [searchClosureStep1]
        apply List.mem_append_right
        exact mem_collectDecompSucc hB X hX
      exact searchClosureStep_succ_mono _ tl t_d X hX1
    · have hB' : B ∈ (searchClosureStep1 prev hd t_d).succedent :=
        searchClosureStep1_succ_mono prev hd t_d B hB
      exact ih (searchClosureStep1 prev hd t_d) hB' htl

/-- Cross-side: if A is in the antecedent and t_c in terms, the SUCCEDENT
decomposition of A (the .2 part) is in the result's succedent. -/
theorem searchClosureStep_decompAntSucc {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (A : FormulaN L) (t_c : Term L)
    (hA : A ∈ prev.antecedent) (ht : t_c ∈ terms) :
    ∀ X ∈ (decomposeAntFormula A t_c t_d).2,
      X ∈ (searchClosureStep prev terms t_d).succedent := by
-- BEGIN PROOF
  intro X hX
  simp only [searchClosureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl] at ht
  | cons hd tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp ht with rfl | htl
    · have hX1 : X ∈ (searchClosureStep1 prev t_c t_d).succedent := by
        simp only [searchClosureStep1]
        apply List.mem_append_left
        apply List.mem_append_right
        exact mem_collectDecompAntSucc hA X hX
      exact searchClosureStep_succ_mono _ tl t_d X hX1
    · have hA' : A ∈ (searchClosureStep1 prev hd t_d).antecedent :=
        searchClosureStep1_ant_mono prev hd t_d A hA
      exact ih (searchClosureStep1 prev hd t_d) hA' htl

/-- Cross-side: if B is in the succedent and t_c in terms, the ANTECEDENT
decomposition of B (the .1 part) is in the result's antecedent. -/
theorem searchClosureStep_decompSuccAnt {L : Language}
    (prev : Sequent L) (terms : List (Term L)) (t_d : Term L)
    (B : FormulaN L) (t_c : Term L)
    (hB : B ∈ prev.succedent) (ht : t_c ∈ terms) :
    ∀ X ∈ (decomposeSuccFormula B t_c t_d).1,
      X ∈ (searchClosureStep prev terms t_d).antecedent := by
-- BEGIN PROOF
  intro X hX
  simp only [searchClosureStep]
  induction terms generalizing prev with
  | nil => simp [List.foldl] at ht
  | cons hd tl ih =>
    simp only [List.foldl]
    rcases List.mem_cons.mp ht with rfl | htl
    · have hX1 : X ∈ (searchClosureStep1 prev t_c t_d).antecedent := by
        simp only [searchClosureStep1]
        apply List.mem_append_right
        exact mem_collectDecompSuccAnt hB X hX
      exact searchClosureStep_ant_mono _ tl t_d X hX1
    · have hB' : B ∈ (searchClosureStep1 prev hd t_d).succedent :=
        searchClosureStep1_succ_mono prev hd t_d B hB
      exact ih (searchClosureStep1 prev hd t_d) hB' htl

-- ===================================================================
-- Membership characterization for searchClosureStep1
-- ===================================================================

/-- Membership in searchClosureStep1 antecedent. -/
theorem mem_searchClosureStep1_ant {L : Language}
    (prev : Sequent L) (t_c t_d : Term L) (A : FormulaN L) :
    A ∈ (searchClosureStep1 prev t_c t_d).antecedent ↔
    A ∈ prev.antecedent ∨
    A ∈ collectDecompAnt prev.antecedent t_c t_d ∨
    A ∈ collectDecompSuccAnt prev.succedent t_c t_d := by
-- BEGIN PROOF
  simp only [searchClosureStep1, List.mem_append, or_assoc]

/-- Membership in searchClosureStep1 succedent. -/
theorem mem_searchClosureStep1_succ {L : Language}
    (prev : Sequent L) (t_c t_d : Term L) (B : FormulaN L) :
    B ∈ (searchClosureStep1 prev t_c t_d).succedent ↔
    B ∈ prev.succedent ∨
    B ∈ collectDecompAntSucc prev.antecedent t_c t_d ∨
    B ∈ collectDecompSucc prev.succedent t_c t_d := by
-- BEGIN PROOF
  simp only [searchClosureStep1, List.mem_append, or_assoc]

-- ===================================================================
-- Branching expansion helpers for type-B formulae
-- ===================================================================

/-- Theorem 5.5.1 (companion): Type-B antecedent component extraction. For a given bit:
- disj X Y in antecedent: bit=0 yields X in ant, bit!=0 yields Y in ant
- impl X Y in antecedent: bit=0 yields X in succ, bit!=0 yields Y in ant
Returns (new antecedent formulas, new succedent formulas). -/
def typeBCompAnt {L : Language} (A : FormulaN L) (bit : Nat) :
    List (FormulaN L) × List (FormulaN L) :=
  match A with
  | .disj X Y => if bit = 0 then ([X], []) else ([Y], [])
  | .impl X Y => if bit = 0 then ([], [X]) else ([Y], [])
  | _ => ([], [])

/-- Theorem 5.5.1 (companion): Type-B succedent component extraction. For a given bit:
- conj X Y in succedent: bit=0 yields X in succ, bit!=0 yields Y in succ
Returns (new antecedent formulas, new succedent formulas). -/
def typeBCompSucc {L : Language} (B : FormulaN L) (bit : Nat) :
    List (FormulaN L) × List (FormulaN L) :=
  match B with
  | .conj X Y => if bit = 0 then ([], [X]) else ([], [Y])
  | _ => ([], [])

/-- Theorem 5.5.1 (companion): Collect type-B antecedent components (new antecedent formulas). -/
def collectBranchAntNew {L : Language} (formulas : List (FormulaN L))
    (bit : Nat) : List (FormulaN L) :=
  formulas.flatMap (fun A => (typeBCompAnt A bit).1)

/-- Theorem 5.5.1 (companion): Collect type-B new succedent formulas from both antecedent and
succedent type-B formulae. -/
def collectBranchSuccNew {L : Language}
    (antFormulas succFormulas : List (FormulaN L))
    (bit : Nat) : List (FormulaN L) :=
  antFormulas.flatMap (fun A => (typeBCompAnt A bit).2) ++
  succFormulas.flatMap (fun B => (typeBCompSucc B bit).2)

/-- Theorem 5.5.1 (companion): Terms whose free variables do not appear as bound variables in any
formula of the sequent. This is the correct term algebra H for the
Hintikka set construction (cf. textbook section 5.4.7): isFreeForN t x A
holds for all t in safeTermsN and all A in the search path. -/
def safeTermsN {L : Language} (seq : Sequent L) : Set (Term L) :=
  fun t => ∀ v, v ∈ termFV t → ∀ A ∈ (seq.antecedent ++ seq.succedent), v ∉ formulaBVN A

/-- Theorem 5.5.1 (companion): The safe terms list for branchStep at a given depth. Filters
Countable.enumerate terms to those in safeTermsN rootSeq (free
variables avoid root sequent's bound variables), plus the fresh
eigenvariable Term.var(freshBase + depth) which is always safe. -/
noncomputable def branchTerms {L : Language} [Countable (Term L)]
    (rootSeq : Sequent L) (depth : Nat) (freshBase : Nat) : List (Term L) :=
  have : ∀ (p : Prop), Decidable p := Classical.propDecidable
  let allTerms := (List.range (depth + 1)).map (Countable.enumerate (α := Term L))
  allTerms.filter (fun t => decide (t ∈ safeTermsN rootSeq))
    ++ [Term.var (freshBase + depth)]

/-- Theorem 5.5.1 (companion): One branching expansion step: apply linear decomposition (type-A/C/D
via searchClosureStep) AND add type-B component selection based on bit.
At depth n, uses safe terms from enumerate 0..n (filtered to safeTermsN
rootSeq) plus the eigenvariable for type-C, and var(freshBase+n) for
type-D, then adds type-B components chosen by bit.

The rootSeq parameter is the root sequent of the search tree. Type-C
substitution terms are restricted to safeTermsN rootSeq to ensure
that no bound variable of the root sequent is introduced as a free
variable in the search path (needed for H5: isFreeFor). -/
noncomputable def branchStep {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth : Nat) (freshBase : Nat)
    (bit : Nat) (rootSeq : Sequent L) : Sequent L :=
  let terms := branchTerms rootSeq depth freshBase
  let linear := searchClosureStep prev terms (Term.var (freshBase + depth))
  { antecedent := linear.antecedent
      ++ collectBranchAntNew prev.antecedent bit
  , succedent := linear.succedent
      ++ collectBranchSuccNew prev.antecedent prev.succedent bit }

/-- Theorem 5.5.1 (companion): Build the sequent at depth n along a path described by f : Nat -> Nat.
At each step, apply branchStep using f(k) as the branching bit at depth k.
This is the branching analogue of searchClosure. The root sequent seq is
passed to branchStep for safe term filtering. -/
noncomputable def branchingNodeSeqF {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f : Nat → Nat)
    : Nat → Sequent L
  | 0 => seq
  | n + 1 =>
    let prev := branchingNodeSeqF seq freshBase f n
    branchStep prev n freshBase (f n) seq

-- -------------------------------------------------------------------
-- Branching monotonicity lemmas
-- -------------------------------------------------------------------

/-- Theorem 5.5.1 (companion): branchStep preserves antecedent membership. -/
theorem branchStep_ant_mono {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat)
    (rootSeq : Sequent L) (A : FormulaN L) :
    A ∈ prev.antecedent →
    A ∈ (branchStep prev depth freshBase bit rootSeq).antecedent := by
-- BEGIN PROOF
  intro hA; simp only [branchStep]
  exact List.mem_append_left _ (searchClosureStep_ant_mono _ _ _ A hA)

/-- Theorem 5.5.1 (companion): branchStep preserves succedent membership. -/
theorem branchStep_succ_mono {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat)
    (rootSeq : Sequent L) (B : FormulaN L) :
    B ∈ prev.succedent →
    B ∈ (branchStep prev depth freshBase bit rootSeq).succedent := by
-- BEGIN PROOF
  intro hB; simp only [branchStep]
  exact List.mem_append_left _ (searchClosureStep_succ_mono _ _ _ B hB)

/-- Formulas at level n appear at level n+1 (antecedent). -/
theorem branchingNodeSeqF_ant_mono {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f : Nat → Nat)
    (n : Nat) (A : FormulaN L) :
    A ∈ (branchingNodeSeqF seq freshBase f n).antecedent →
    A ∈ (branchingNodeSeqF seq freshBase f (n + 1)).antecedent := by
-- BEGIN PROOF
  intro hA; simp only [branchingNodeSeqF]
  exact branchStep_ant_mono _ n freshBase (f n) seq A hA

/-- Formulas at level n appear at level n+1 (succedent). -/
theorem branchingNodeSeqF_succ_mono {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f : Nat → Nat)
    (n : Nat) (B : FormulaN L) :
    B ∈ (branchingNodeSeqF seq freshBase f n).succedent →
    B ∈ (branchingNodeSeqF seq freshBase f (n + 1)).succedent := by
-- BEGIN PROOF
  intro hB; simp only [branchingNodeSeqF]
  exact branchStep_succ_mono _ n freshBase (f n) seq B hB

/-- Monotonicity extended: antecedent formulas at level n appear at any
level m >= n. -/
theorem branchingNodeSeqF_ant_mono_le {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f : Nat → Nat)
    {n m : Nat} (h : n ≤ m) (A : FormulaN L) :
    A ∈ (branchingNodeSeqF seq freshBase f n).antecedent →
    A ∈ (branchingNodeSeqF seq freshBase f m).antecedent := by
-- BEGIN PROOF
  intro hA
  induction m with
  | zero => exact Nat.le_zero.mp h ▸ hA
  | succ k ih =>
    by_cases hk : n ≤ k
    · exact branchingNodeSeqF_ant_mono seq freshBase f k A (ih hk)
    · have : n = k + 1 := by omega
      exact this ▸ hA

/-- Monotonicity extended: succedent formulas at level n appear at any
level m >= n. -/
theorem branchingNodeSeqF_succ_mono_le {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f : Nat → Nat)
    {n m : Nat} (h : n ≤ m) (B : FormulaN L) :
    B ∈ (branchingNodeSeqF seq freshBase f n).succedent →
    B ∈ (branchingNodeSeqF seq freshBase f m).succedent := by
-- BEGIN PROOF
  intro hB
  induction m with
  | zero => exact Nat.le_zero.mp h ▸ hB
  | succ k ih =>
    by_cases hk : n ≤ k
    · exact branchingNodeSeqF_succ_mono seq freshBase f k B (ih hk)
    · have : n = k + 1 := by omega
      exact this ▸ hB

-- -------------------------------------------------------------------
-- Branching type-B decomposition lemmas
-- -------------------------------------------------------------------

/-- disj X Y in antecedent at depth k => X in antecedent at depth k+1
when bit=0. -/
theorem branchStep_disj_comp0 {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase : Nat) (rootSeq : Sequent L)
    (X Y : FormulaN L) :
    FormulaN.disj X Y ∈ prev.antecedent →
    X ∈ (branchStep prev depth freshBase 0 rootSeq).antecedent := by
-- BEGIN PROOF
  intro hF; simp only [branchStep]
  apply List.mem_append_right
  simp only [collectBranchAntNew, List.mem_flatMap]
  exact ⟨FormulaN.disj X Y, hF, by simp [typeBCompAnt]⟩

/-- disj X Y in antecedent at depth k => Y in antecedent at depth k+1
when bit != 0. -/
theorem branchStep_disj_comp1 {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat) (rootSeq : Sequent L)
    (X Y : FormulaN L)
    (hbit : bit ≠ 0) :
    FormulaN.disj X Y ∈ prev.antecedent →
    Y ∈ (branchStep prev depth freshBase bit rootSeq).antecedent := by
-- BEGIN PROOF
  intro hF; simp only [branchStep]
  apply List.mem_append_right
  simp only [collectBranchAntNew, List.mem_flatMap]
  exact ⟨FormulaN.disj X Y, hF, by simp [typeBCompAnt, hbit]⟩

/-- impl X Y in antecedent at depth k => X in succedent at depth k+1
when bit=0 (comp1 of tImpl is falseF X). -/
theorem branchStep_impl_comp0 {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase : Nat) (rootSeq : Sequent L)
    (X Y : FormulaN L) :
    FormulaN.impl X Y ∈ prev.antecedent →
    X ∈ (branchStep prev depth freshBase 0 rootSeq).succedent := by
-- BEGIN PROOF
  intro hF; simp only [branchStep]
  apply List.mem_append_right
  simp only [collectBranchSuccNew, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨FormulaN.impl X Y, hF, by simp [typeBCompAnt]⟩

/-- impl X Y in antecedent at depth k => Y in antecedent at depth k+1
when bit != 0 (comp2 of tImpl is trueF Y). -/
theorem branchStep_impl_comp1 {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat) (rootSeq : Sequent L)
    (X Y : FormulaN L)
    (hbit : bit ≠ 0) :
    FormulaN.impl X Y ∈ prev.antecedent →
    Y ∈ (branchStep prev depth freshBase bit rootSeq).antecedent := by
-- BEGIN PROOF
  intro hF; simp only [branchStep]
  apply List.mem_append_right
  simp only [collectBranchAntNew, List.mem_flatMap]
  exact ⟨FormulaN.impl X Y, hF, by simp [typeBCompAnt, hbit]⟩

/-- conj X Y in succedent at depth k => X in succedent at depth k+1
when bit=0 (comp1 of fConj is falseF X). -/
theorem branchStep_conj_succ_comp0 {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase : Nat) (rootSeq : Sequent L)
    (X Y : FormulaN L) :
    FormulaN.conj X Y ∈ prev.succedent →
    X ∈ (branchStep prev depth freshBase 0 rootSeq).succedent := by
-- BEGIN PROOF
  intro hF; simp only [branchStep]
  apply List.mem_append_right
  simp only [collectBranchSuccNew, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨FormulaN.conj X Y, hF, by simp [typeBCompSucc]⟩

/-- conj X Y in succedent at depth k => Y in succedent at depth k+1
when bit != 0 (comp2 of fConj is falseF Y). -/
theorem branchStep_conj_succ_comp1 {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat) (rootSeq : Sequent L)
    (X Y : FormulaN L)
    (hbit : bit ≠ 0) :
    FormulaN.conj X Y ∈ prev.succedent →
    Y ∈ (branchStep prev depth freshBase bit rootSeq).succedent := by
-- BEGIN PROOF
  intro hF; simp only [branchStep]
  apply List.mem_append_right
  simp only [collectBranchSuccNew, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨FormulaN.conj X Y, hF, by simp [typeBCompSucc, hbit]⟩

-- -------------------------------------------------------------------
-- Branching type-A/C/D decomposition through branchStep
-- -------------------------------------------------------------------

/-- Linear decomposition of antecedent formulas propagates through
branchStep (the searchClosureStep part). -/
theorem branchStep_decompAnt {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat) (rootSeq : Sequent L)
    (A : FormulaN L) (t_c : Term L)
    (hA : A ∈ prev.antecedent)
    (ht : t_c ∈ branchTerms rootSeq depth freshBase) :
    ∀ X ∈ (decomposeAntFormula A t_c (Term.var (freshBase + depth))).1,
      X ∈ (branchStep prev depth freshBase bit rootSeq).antecedent := by
-- BEGIN PROOF
  intro X hX; simp only [branchStep]
  exact List.mem_append_left _
    (searchClosureStep_decompAnt prev _ (Term.var (freshBase + depth))
      A t_c hA ht X hX)

/-- Cross-side: antecedent formula decomposition producing succedent
formulas propagates through branchStep. -/
theorem branchStep_decompAntSucc {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat) (rootSeq : Sequent L)
    (A : FormulaN L) (t_c : Term L)
    (hA : A ∈ prev.antecedent)
    (ht : t_c ∈ branchTerms rootSeq depth freshBase) :
    ∀ X ∈ (decomposeAntFormula A t_c (Term.var (freshBase + depth))).2,
      X ∈ (branchStep prev depth freshBase bit rootSeq).succedent := by
-- BEGIN PROOF
  intro X hX; simp only [branchStep]
  exact List.mem_append_left _
    (searchClosureStep_decompAntSucc prev _ (Term.var (freshBase + depth))
      A t_c hA ht X hX)

/-- Linear decomposition of succedent formulas propagates through
branchStep. -/
theorem branchStep_decompSucc {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat) (rootSeq : Sequent L)
    (B : FormulaN L) (t_c : Term L)
    (hB : B ∈ prev.succedent)
    (ht : t_c ∈ branchTerms rootSeq depth freshBase) :
    ∀ X ∈ (decomposeSuccFormula B t_c (Term.var (freshBase + depth))).2,
      X ∈ (branchStep prev depth freshBase bit rootSeq).succedent := by
-- BEGIN PROOF
  intro X hX; simp only [branchStep]
  exact List.mem_append_left _
    (searchClosureStep_decompSucc prev _ (Term.var (freshBase + depth))
      B t_c hB ht X hX)

/-- Cross-side: succedent formula decomposition producing antecedent
formulas propagates through branchStep. -/
theorem branchStep_decompSuccAnt {L : Language} [Countable (Term L)]
    (prev : Sequent L) (depth freshBase bit : Nat) (rootSeq : Sequent L)
    (B : FormulaN L) (t_c : Term L)
    (hB : B ∈ prev.succedent)
    (ht : t_c ∈ branchTerms rootSeq depth freshBase) :
    ∀ X ∈ (decomposeSuccFormula B t_c (Term.var (freshBase + depth))).1,
      X ∈ (branchStep prev depth freshBase bit rootSeq).antecedent := by
-- BEGIN PROOF
  intro X hX; simp only [branchStep]
  exact List.mem_append_left _
    (searchClosureStep_decompSuccAnt prev _ (Term.var (freshBase + depth))
      B t_c hB ht X hX)

-- -------------------------------------------------------------------
-- Extensionality and path-address equivalence
-- -------------------------------------------------------------------

/-- Theorem 5.5.1 (companion): branchingNodeSeqF depends only on f at indices < n: if f and g
agree on [0, n), the result is the same. -/
theorem branchingNodeSeqF_ext {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f g : Nat → Nat) (n : Nat)
    (heq : ∀ i, i < n → f i = g i) :
    branchingNodeSeqF seq freshBase f n =
    branchingNodeSeqF seq freshBase g n := by
-- BEGIN PROOF
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [branchingNodeSeqF]
    have hk : f k = g k := heq k (by omega)
    have hprev := ih (fun i hi => heq i (by omega))
    rw [hprev, hk]

/-- Theorem 5.5.1 (companion): The node sequent at address List.ofFn (Fin n => f i) equals
branchingNodeSeqF seq freshBase f n. This connects the address-based
nodeSequent to the path-function-based branchingNodeSeqF. -/
theorem branchingNodeSeqF_ofFn_eq {L : Language} [Countable (Term L)]
    (seq : Sequent L) (freshBase : Nat) (f : Nat → Nat) (n : Nat) :
    branchingNodeSeqF seq freshBase
      (fun i => (List.ofFn (fun j : Fin n => f j)).getD i 0) n =
    branchingNodeSeqF seq freshBase f n := by
-- BEGIN PROOF
  apply branchingNodeSeqF_ext
  intro i hi
  simp [List.getD, hi]

-- ===================================================================
-- SearchTreeData: Normalized search tree data structure
-- ===================================================================

/-- Theorem 5.5.1 (companion, normalized): A search tree data structure over
FormulaN/Sequent, containing the tree domain, node sequents, node
states, and structural invariants. The path Hintikka properties
(H0-H6) and finite-valid-to-proof conversion are stated as separate
sorry'd theorems below, following the textbook's separation of the
search tree construction from its properties. -/
structure SearchTreeData (L : Language) [Countable (Term L)] (seq : Sequent L) where
  /-- The tree domain of the search tree -/
  treeDom : LCS.TreeDomain
  /-- The sequent at each tree address -/
  nodeSequent : (addr : TreeAddr) → addr ∈ treeDom.dom → Sequent L
  /-- The search state at each tree address -/
  nodeState : (addr : TreeAddr) → addr ∈ treeDom.dom → SearchState L
  /-- Root has the input sequent -/
  root_sequent : nodeSequent [] treeDom.root_mem = seq
  /-- Axiom nodes are leaves: if the sequent at u is an axiom, then
      u has no children in the search tree -/
  axiom_is_leaf : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom),
    isAxiom (nodeSequent u hu) →
    ¬ ((u ++ [0]) ∈ treeDom.dom)
  /-- The tree is finitely branching -/
  finBranching : treeDom.FinitelyBranching
  /-- Non-axiom nodes have at least one child -/
  non_axiom_has_child : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom),
    ¬ isAxiom (nodeSequent u hu) →
    (u ++ [0]) ∈ treeDom.dom
  /-- The input sequent has no free-bound variable overlap -/
  input_noFreeBound : noFreeBound seq
  /-- The input sequent has cross-formula free/bound disjointness
      (textbook section 5.4.7 assumption). -/
  input_crossNoFreeBound : crossNoFreeBound seq
  /-- The input sequent has no eq_ formulas -/
  input_seqNoEq : seqNoEq seq
  /-- Antecedent monotonicity along paths: parent antecedent ⊆ child antecedent -/
  path_ant_mono : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom) (i : Nat)
    (hc : (u ++ [i]) ∈ treeDom.dom) (A : FormulaN L),
    A ∈ (nodeSequent u hu).antecedent →
    A ∈ (nodeSequent (u ++ [i]) hc).antecedent
  /-- Succedent monotonicity along paths: parent succedent ⊆ child succedent -/
  path_succ_mono : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom) (i : Nat)
    (hc : (u ++ [i]) ∈ treeDom.dom) (B : FormulaN L),
    B ∈ (nodeSequent u hu).succedent →
    B ∈ (nodeSequent (u ++ [i]) hc).succedent
  /-- Non-axiom nodes have no eq_ formulas. (Axiom leaf nodes may
      contain eq_ sentinels, but they are never on infinite paths.) -/
  node_seqNoEq : ∀ (u : TreeAddr) (hu : u ∈ treeDom.dom),
    ¬ isAxiom (nodeSequent u hu) → seqNoEq (nodeSequent u hu)
  /-- The base for fresh variable generation -/
  freshBase : Nat
  /-- freshBase is large enough to avoid all bound variables in seq -/
  freshBase_bound : ∀ v, ∀ A ∈ (seq.antecedent ++ seq.succedent), v ∈ formulaBVN A → v < freshBase
  /-- Path expansion: along any infinite path f, the nodeSequent at depth
      n+1 equals branchStep applied to the nodeSequent at depth n. -/
  path_expansion : ∀ (f : Nat → Nat) (n : Nat)
    (hPath : ∀ m, (List.ofFn (fun i : Fin m => f i)) ∈ treeDom.dom),
    nodeSequent (List.ofFn (fun i : Fin (n + 1) => f i)) (hPath (n + 1)) =
    branchStep (nodeSequent (List.ofFn (fun i : Fin n => f i)) (hPath n)) n freshBase (f n) seq
  /-- Provability extraction from finite tree: if the search tree domain
      is finite then the input sequent is G-provable under the §5.4.8
      standing assumption. Populated by buildSearchTree: axiom case gives
      direct proof, provable case delegates, not-provable case derives
      contradiction (the tree is actually infinite, so IsFinite yields
      False). -/
  provable_if_finite : treeDom.IsFinite → sequentProvableExt seq

-- ===================================================================
-- SearchTreeData.pathSignedSet: helper for path signed set
-- ===================================================================

/-- Theorem 5.4.1 (normalized, helper): The signed formula set along
a path f : Nat -> Nat in a SearchTreeData. Collects all signed
formulae from the antecedent (as trueF) and succedent (as falseF) of
every sequent along the path. This avoids repeating the `let S := ...`
definition in every path property theorem. -/
def SearchTreeData.pathSignedSet {L : Language} [Countable (Term L)] {seq : Sequent L}
    (w : SearchTreeData L seq) (f : Nat → Nat)
    (_hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    Set (SignedFormula L) := fun sf =>
  ∃ n : Nat, ∃ (h : (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom),
    let seq_n := w.nodeSequent (List.ofFn (fun i : Fin n => f i)) h
    (∃ A ∈ seq_n.antecedent, sf = SignedFormula.trueF A) ∨
    (∃ B ∈ seq_n.succedent, sf = SignedFormula.falseF B)

-- ===================================================================
-- Path infrastructure lemmas
-- ===================================================================

/-- List.ofFn (Fin (n+1) => f) = List.ofFn (Fin n => f) ++ [f n].
Connects the address at depth n+1 to the address at depth n
via appending the branching bit. -/
theorem ofFn_succ_append (f : Nat → Nat) (n : Nat) :
    List.ofFn (fun i : Fin (n + 1) => f i) =
    List.ofFn (fun i : Fin n => f i) ++ [f n] := by
-- BEGIN PROOF
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn]
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simp; exact hi)]
      simp [List.getElem_ofFn]
    · have hieq : i = n := by omega
      subst hieq
      rw [List.getElem_append_right (by simp)]
      simp [List.length_ofFn]

/-- If u ++ [i] is in a tree domain, so is u ++ [0].
Uses left_sibling_closed iteratively. -/
theorem dom_child_zero (td : LCS.TreeDomain) (u : LCS.TreeAddr) (i : Nat)
    (h : (u ++ [i]) ∈ td.dom) : (u ++ [0]) ∈ td.dom := by
-- BEGIN PROOF
  induction i with
  | zero => exact h
  | succ k ih => exact ih (td.left_sibling_closed u k h)

/-- Multi-step antecedent monotonicity along a path. If A is in the
antecedent at depth n and n ≤ m, then A is in the antecedent at
depth m, using path_ant_mono at each step. -/
theorem path_ant_mono_le {L : Language} [Countable (Term L)] {seq : Sequent L}
    (w : SearchTreeData L seq) (f : Nat → Nat)
    (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom)
    {n m : Nat} (h : n ≤ m) (A : FormulaN L)
    (hA : A ∈ (w.nodeSequent _ (hPath n)).antecedent) :
    A ∈ (w.nodeSequent _ (hPath m)).antecedent := by
-- BEGIN PROOF
  induction m with
  | zero => exact Nat.le_zero.mp h ▸ hA
  | succ k ih =>
    by_cases hk : n ≤ k
    · have hAk := ih hk
      have haddr := ofFn_succ_append f k
      have hc := haddr ▸ hPath (k + 1)
      have hAmono := w.path_ant_mono _ (hPath k) (f k) hc A hAk
      have hseq_eq : w.nodeSequent (List.ofFn (fun i : Fin k => f i) ++ [f k]) hc =
          w.nodeSequent (List.ofFn (fun i : Fin (k + 1) => f i)) (hPath (k + 1)) := by
        congr 1; exact haddr.symm
      rw [hseq_eq] at hAmono; exact hAmono
    · cases (show n = k + 1 by omega); exact hA

/-- Multi-step succedent monotonicity along a path. Same as
path_ant_mono_le but for the succedent. -/
theorem path_succ_mono_le {L : Language} [Countable (Term L)] {seq : Sequent L}
    (w : SearchTreeData L seq) (f : Nat → Nat)
    (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom)
    {n m : Nat} (h : n ≤ m) (B : FormulaN L)
    (hB : B ∈ (w.nodeSequent _ (hPath n)).succedent) :
    B ∈ (w.nodeSequent _ (hPath m)).succedent := by
-- BEGIN PROOF
  induction m with
  | zero => exact Nat.le_zero.mp h ▸ hB
  | succ k ih =>
    by_cases hk : n ≤ k
    · have hBk := ih hk
      have haddr := ofFn_succ_append f k
      have hc := haddr ▸ hPath (k + 1)
      have hBmono := w.path_succ_mono _ (hPath k) (f k) hc B hBk
      have hseq_eq : w.nodeSequent (List.ofFn (fun i : Fin k => f i) ++ [f k]) hc =
          w.nodeSequent (List.ofFn (fun i : Fin (k + 1) => f i)) (hPath (k + 1)) := by
        congr 1; exact haddr.symm
      rw [hseq_eq] at hBmono; exact hBmono
    · cases (show n = k + 1 by omega); exact hB

-- ===================================================================
-- Theorem 5.4.1 properties: separate sorry'd theorems
-- ===================================================================

/-- Theorem 5.5.1 (companion, H1/H2): Along any infinite path in the search tree,
the signed formulae satisfy the propositional Hintikka conditions:
type-A formulae have both components, and type-B formulae have at
least one component. -/
theorem searchTree_path_hintikka_propositional {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    (∀ (a : TypeA L), a.toSigned ∈ S → a.comp1 ∈ S ∧ a.comp2 ∈ S) ∧
    (∀ (b : TypeB L), b.toSigned ∈ S → b.comp1 ∈ S ∨ b.comp2 ∈ S) := by
-- BEGIN PROOF
  intro S
  -- Helper: the freshVar is always in branchTerms (guaranteed non-empty entry)
  have freshVar_in : ∀ k, Term.var (w.freshBase + k) ∈
      branchTerms seq k w.freshBase := by
    intro k; simp only [branchTerms]
    exact List.mem_append_right _ (List.Mem.head _)
  constructor
  · -- H1: TypeA decomposition
    intro a ha
    cases a with
    | tConj X Y =>
      -- trueF (conj X Y) ∈ S: conj X Y in antecedent at depth k
      obtain ⟨k, _, hAk⟩ := ha
      have hAnt : FormulaN.conj X Y ∈ (w.nodeSequent _ (hPath k)).antecedent := by
        rcases hAk with ⟨A, hA, hAeq⟩ | ⟨B, _, hBeq⟩
        · exact SignedFormula.trueF.inj hAeq ▸ hA
        · exact absurd hBeq (by intro h; cases h)
      have hexp := w.path_expansion f k hPath
      have hX : X ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent :=
        branchStep_decompAnt _ k w.freshBase (f k) seq _ _ hAnt (freshVar_in k) X
          (by simp [decomposeAntFormula])
      have hY : Y ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent :=
        branchStep_decompAnt _ k w.freshBase (f k) seq _ _ hAnt (freshVar_in k) Y
          (by simp [decomposeAntFormula])
      rw [← hexp] at hX hY
      exact ⟨⟨k + 1, hPath (k + 1), Or.inl ⟨X, hX, rfl⟩⟩,
             ⟨k + 1, hPath (k + 1), Or.inl ⟨Y, hY, rfl⟩⟩⟩
    | fDisj X Y =>
      -- falseF (disj X Y) ∈ S: disj X Y in succedent at depth k
      obtain ⟨k, _, hAk⟩ := ha
      have hSucc : FormulaN.disj X Y ∈ (w.nodeSequent _ (hPath k)).succedent := by
        rcases hAk with ⟨A, _, hAeq⟩ | ⟨B, hB, hBeq⟩
        · exact absurd hAeq (by intro h; cases h)
        · exact SignedFormula.falseF.inj hBeq ▸ hB
      have hexp := w.path_expansion f k hPath
      have hX : X ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent :=
        branchStep_decompSucc _ k w.freshBase (f k) seq _ _ hSucc (freshVar_in k) X
          (by simp [decomposeSuccFormula])
      have hY : Y ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent :=
        branchStep_decompSucc _ k w.freshBase (f k) seq _ _ hSucc (freshVar_in k) Y
          (by simp [decomposeSuccFormula])
      rw [← hexp] at hX hY
      exact ⟨⟨k + 1, hPath (k + 1), Or.inr ⟨X, hX, rfl⟩⟩,
             ⟨k + 1, hPath (k + 1), Or.inr ⟨Y, hY, rfl⟩⟩⟩
    | fImpl X Y =>
      -- falseF (impl X Y) ∈ S: impl X Y in succedent at depth k
      obtain ⟨k, _, hAk⟩ := ha
      have hSucc : FormulaN.impl X Y ∈ (w.nodeSequent _ (hPath k)).succedent := by
        rcases hAk with ⟨A, _, hAeq⟩ | ⟨B, hB, hBeq⟩
        · exact absurd hAeq (by intro h; cases h)
        · exact SignedFormula.falseF.inj hBeq ▸ hB
      have hexp := w.path_expansion f k hPath
      -- X to antecedent (cross-side), Y to succedent
      have hX : X ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent :=
        branchStep_decompSuccAnt _ k w.freshBase (f k) seq _ _ hSucc (freshVar_in k) X
          (by simp [decomposeSuccFormula])
      have hY : Y ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent :=
        branchStep_decompSucc _ k w.freshBase (f k) seq _ _ hSucc (freshVar_in k) Y
          (by simp [decomposeSuccFormula])
      rw [← hexp] at hX hY
      exact ⟨⟨k + 1, hPath (k + 1), Or.inl ⟨X, hX, rfl⟩⟩,
             ⟨k + 1, hPath (k + 1), Or.inr ⟨Y, hY, rfl⟩⟩⟩
    | tNeg X =>
      -- trueF (neg X) ∈ S: neg X in antecedent at depth k
      -- comp1 = falseF X, comp2 = falseF X
      obtain ⟨k, _, hAk⟩ := ha
      have hAnt : FormulaN.neg X ∈ (w.nodeSequent _ (hPath k)).antecedent := by
        rcases hAk with ⟨A, hA, hAeq⟩ | ⟨B, _, hBeq⟩
        · exact SignedFormula.trueF.inj hAeq ▸ hA
        · exact absurd hBeq (by intro h; cases h)
      have hexp := w.path_expansion f k hPath
      -- X goes to succedent (cross-side)
      have hX : X ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent :=
        branchStep_decompAntSucc _ k w.freshBase (f k) seq _ _ hAnt (freshVar_in k) X
          (by simp [decomposeAntFormula])
      rw [← hexp] at hX
      exact ⟨⟨k + 1, hPath (k + 1), Or.inr ⟨X, hX, rfl⟩⟩,
             ⟨k + 1, hPath (k + 1), Or.inr ⟨X, hX, rfl⟩⟩⟩
    | fNeg X =>
      -- falseF (neg X) ∈ S: neg X in succedent at depth k
      -- comp1 = trueF X, comp2 = trueF X
      obtain ⟨k, _, hAk⟩ := ha
      have hSucc : FormulaN.neg X ∈ (w.nodeSequent _ (hPath k)).succedent := by
        rcases hAk with ⟨A, _, hAeq⟩ | ⟨B, hB, hBeq⟩
        · exact absurd hAeq (by intro h; cases h)
        · exact SignedFormula.falseF.inj hBeq ▸ hB
      have hexp := w.path_expansion f k hPath
      -- X goes to antecedent (cross-side)
      have hX : X ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent :=
        branchStep_decompSuccAnt _ k w.freshBase (f k) seq _ _ hSucc (freshVar_in k) X
          (by simp [decomposeSuccFormula])
      rw [← hexp] at hX
      exact ⟨⟨k + 1, hPath (k + 1), Or.inl ⟨X, hX, rfl⟩⟩,
             ⟨k + 1, hPath (k + 1), Or.inl ⟨X, hX, rfl⟩⟩⟩
  · -- H2: TypeB decomposition
    intro b hb
    cases b with
    | tDisj X Y =>
      -- trueF (disj X Y) ∈ S: disj X Y in antecedent at depth k
      obtain ⟨k, _, hAk⟩ := hb
      have hAnt : FormulaN.disj X Y ∈ (w.nodeSequent _ (hPath k)).antecedent := by
        rcases hAk with ⟨A, hA, hAeq⟩ | ⟨B, _, hBeq⟩
        · exact SignedFormula.trueF.inj hAeq ▸ hA
        · exact absurd hBeq (by intro h; cases h)
      have hexp := w.path_expansion f k hPath
      by_cases hbit : f k = 0
      · have hX : X ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent := by
          rw [hbit]; exact branchStep_disj_comp0 _ k w.freshBase seq X Y hAnt
        rw [← hexp] at hX
        exact Or.inl ⟨k + 1, hPath (k + 1), Or.inl ⟨X, hX, rfl⟩⟩
      · have hY : Y ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent :=
          branchStep_disj_comp1 _ k w.freshBase (f k) seq X Y hbit hAnt
        rw [← hexp] at hY
        exact Or.inr ⟨k + 1, hPath (k + 1), Or.inl ⟨Y, hY, rfl⟩⟩
    | tImpl X Y =>
      -- trueF (impl X Y) ∈ S: impl X Y in antecedent at depth k
      -- comp1 = falseF X, comp2 = trueF Y
      obtain ⟨k, _, hAk⟩ := hb
      have hAnt : FormulaN.impl X Y ∈ (w.nodeSequent _ (hPath k)).antecedent := by
        rcases hAk with ⟨A, hA, hAeq⟩ | ⟨B, _, hBeq⟩
        · exact SignedFormula.trueF.inj hAeq ▸ hA
        · exact absurd hBeq (by intro h; cases h)
      have hexp := w.path_expansion f k hPath
      by_cases hbit : f k = 0
      · -- bit=0: X in succedent (comp1 = falseF X)
        have hX : X ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent := by
          rw [hbit]; exact branchStep_impl_comp0 _ k w.freshBase seq X Y hAnt
        rw [← hexp] at hX
        exact Or.inl ⟨k + 1, hPath (k + 1), Or.inr ⟨X, hX, rfl⟩⟩
      · -- bit!=0: Y in antecedent (comp2 = trueF Y)
        have hY : Y ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).antecedent :=
          branchStep_impl_comp1 _ k w.freshBase (f k) seq X Y hbit hAnt
        rw [← hexp] at hY
        exact Or.inr ⟨k + 1, hPath (k + 1), Or.inl ⟨Y, hY, rfl⟩⟩
    | fConj X Y =>
      -- falseF (conj X Y) ∈ S: conj X Y in succedent at depth k
      -- comp1 = falseF X, comp2 = falseF Y
      obtain ⟨k, _, hAk⟩ := hb
      have hSucc : FormulaN.conj X Y ∈ (w.nodeSequent _ (hPath k)).succedent := by
        rcases hAk with ⟨A, _, hAeq⟩ | ⟨B, hB, hBeq⟩
        · exact absurd hAeq (by intro h; cases h)
        · exact SignedFormula.falseF.inj hBeq ▸ hB
      have hexp := w.path_expansion f k hPath
      by_cases hbit : f k = 0
      · -- bit=0: X in succedent
        have hX : X ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent := by
          rw [hbit]; exact branchStep_conj_succ_comp0 _ k w.freshBase seq X Y hSucc
        rw [← hexp] at hX
        exact Or.inl ⟨k + 1, hPath (k + 1), Or.inr ⟨X, hX, rfl⟩⟩
      · -- bit!=0: Y in succedent
        have hY : Y ∈ (branchStep (w.nodeSequent _ (hPath k)) k w.freshBase (f k) seq).succedent :=
          branchStep_conj_succ_comp1 _ k w.freshBase (f k) seq X Y hbit hSucc
        rw [← hexp] at hY
        exact Or.inr ⟨k + 1, hPath (k + 1), Or.inr ⟨Y, hY, rfl⟩⟩

/-- Theorem 5.5.1 (companion, H0): Along any infinite path in the search tree,
no atomic formula and its conjugate are both in the signed set. -/
theorem searchTree_path_no_complementary_atoms {L : Language} [Countable (Term L)]
    {seq : Sequent L} (w : SearchTreeData L seq)
    (f : Nat → Nat) (hPath : ∀ n, (List.ofFn (fun i : Fin n => f i)) ∈ w.treeDom.dom) :
    let S := w.pathSignedSet f hPath
    ∀ (A : FormulaN L), A.isAtomic = true →
      ¬(SignedFormula.trueF A ∈ S ∧ SignedFormula.falseF A ∈ S) := by
-- BEGIN PROOF
  intro S A _hAt ⟨⟨n, _hn, hAn⟩, ⟨m, _hm, hAm⟩⟩
  -- Extract: A ∈ antecedent at depth n (from trueF A ∈ S)
  have hAnt_n : A ∈ (w.nodeSequent _ (hPath n)).antecedent := by
    rcases hAn with ⟨X, hX, hXeq⟩ | ⟨Y, _hY, hYeq⟩
    · exact SignedFormula.trueF.inj hXeq ▸ hX
    · exact absurd hYeq (by intro h; cases h)
  -- Extract: A ∈ succedent at depth m (from falseF A ∈ S)
  have hSucc_m : A ∈ (w.nodeSequent _ (hPath m)).succedent := by
    rcases hAm with ⟨X, _hX, hXeq⟩ | ⟨Y, hY, hYeq⟩
    · exact absurd hXeq (by intro h; cases h)
    · exact SignedFormula.falseF.inj hYeq ▸ hY
  -- Use monotonicity to get both at depth N = max(n, m)
  let N := max n m
  have hAnt_N := path_ant_mono_le w f hPath (Nat.le_max_left n m) A hAnt_n
  have hSucc_N := path_succ_mono_le w f hPath (Nat.le_max_right n m) A hSucc_m
  -- isAxiom at depth N
  have hAx : isAxiom (w.nodeSequent _ (hPath N)) := ⟨A, hAnt_N, hSucc_N⟩
  -- axiom_is_leaf: ¬(ofFn(N) ++ [0] ∈ dom)
  have hNoChild := w.axiom_is_leaf _ (hPath N) hAx
  -- But path continues: ofFn(N+1) = ofFn(N) ++ [f N] ∈ dom
  have haddr := ofFn_succ_append f N
  have hChild : (List.ofFn (fun i : Fin N => f i)) ++ [f N] ∈ w.treeDom.dom :=
    haddr ▸ hPath (N + 1)
  -- By dom_child_zero: ofFn(N) ++ [0] ∈ dom
  have hChild0 := dom_child_zero w.treeDom _ (f N) hChild
  -- Contradiction
  exact hNoChild hChild0

end LCS.FirstOrder.Gentzen.Hintikka
end

