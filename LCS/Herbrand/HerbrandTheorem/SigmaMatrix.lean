import LCS.Item
import LCS.CutElim.Hauptsatz
import LCS.Util
import LCS.FirstOrder.Semantics.Subformulae
import LCS.Herbrand.PrenexForm
import LCS.Herbrand.SharpenedHauptsatz.Theorem
import LCS.CutElim.Interpolation.Equality
import LCS.Herbrand.HerbrandTheorem.SkolemFunctions
import LCS.Herbrand.HerbrandTheorem.Substitutions
import Attach
import LCS.Herbrand.HerbrandTheorem.SigmaMatrix.ProofsStamp

/-! # Herbrand.HerbrandTheorem.SigmaMatrix
    Chapter 7, Section 5.4: Definition 7.5.4, the sigma-matrix of the
    functional form of a substitution pair up to i, with the new variables
    naming the Herbrand terms, and its agreement with the original matrix.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.HerbrandTheorem
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.Semantics.Subformulae
open LCS.Herbrand.PrenexForm
open LCS.Herbrand.SharpenedHauptsatz.Theorem
open LCS.CutElim.LK
open LCS.CutElim.LKe.Equivalence
open LCS.FirstOrder.Gentzen
open LCS.CutElim.Interpolation.Equality

-- ===================================================================
-- Theorem 7.5.1 (required helper): newVariable
-- ===================================================================

/-- All variable indices occurring in Γ, including free occurrences and every
binder occurrence. Fresh proof-local names avoid this entire finite list. -/
@[blueprint "chap7__definition_7_5_4"]
def sourceVariableIndices {L : Language} (Γ : List (FormulaN L)) : List Nat :=
  Γ.flatMap (fun A => formulaFreeVarIndices A ++ formulaBoundVarIndices A)

/-- A finite proof-local assignment of distinct fresh variables to terms.
Only terms in the supplied domain have names; the source is the whole Γ. -/
@[blueprint "chap7__definition_7_5_4"]
structure FreshTermNames {L : Language} (Γ : List (FormulaN L))
    (terms : List (Term (validitySkolemLanguage Γ))) : Type where
  name : (t : Term (validitySkolemLanguage Γ)) → t ∈ terms → Nat
  injective : ∀ t u (ht : t ∈ terms) (hu : u ∈ terms),
    name t ht = name u hu → t = u
  fresh : ∀ t (ht : t ∈ terms) x, x ∈ sourceVariableIndices Γ → name t ht ≠ x

/-- The name of a term in a finite proof-local domain. No value is supplied
for a term outside that domain. -/
@[blueprint "chap7__definition_7_5_4"]
def newVariable {L : Language} {Γ : List (FormulaN L)}
    {terms : List (Term (validitySkolemLanguage Γ))}
    (names : FreshTermNames Γ terms) (t : Term (validitySkolemLanguage Γ))
    (ht : t ∈ terms) : Nat := names.name t ht

/-- All substituted universal-occurrence terms requested by this σ-matrix.
The list includes vacuous universals even when their terms do not occur in HT. -/
@[blueprint "chap7__definition_7_5_4"]
def sigmaMatrixRequiredTerms {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ)) :
    List (Term (validitySkolemLanguage Γ)) :=
  let prefix_ := prenexPrefix (Γ.get j)
  (List.ofFn (fun p : Fin prefix_.length => p)).flatMap fun p =>
    match h : (prefix_.get p).1 with
    | .universal => [Substitution.applyTerm sigma (skolemTerm sd ⟨j, p, h⟩)]
    | .existential => []

/-- Every actual universal position contributes its required term. -/
@[blueprint "chap7__definition_7_5_4"]
theorem sigmaMatrixTerm_mem {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    (p : Fin (prenexPrefix (Γ.get j)).length)
    (h : ((prenexPrefix (Γ.get j)).get p).1 = .universal) :
    Substitution.applyTerm sigma (skolemTerm sd ⟨j, p, h⟩) ∈
      sigmaMatrixRequiredTerms sd j sigma

/-- The finite naming table covers every term used by this σ-matrix.
One shared table may cover the requirements of many proof-local pairs. -/
@[blueprint "chap7__definition_7_5_4"]
def SigmaMatrixNamesCover {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    {terms : List (Term (validitySkolemLanguage Γ))}
    (_names : FreshTermNames Γ terms) : Prop :=
  ∀ t, t ∈ sigmaMatrixRequiredTerms sd j sigma → t ∈ terms

-- ===================================================================
-- Theorem 7.5.1 (required helper): sigmaMatrix
-- ===================================================================

/-- Definition 7.5.4: stages of the σ-matrix for the fixed source sentence.
Stage zero replaces every universal variable in the original embedded matrix
by its proof-local name. Stage k+1 is obtained from stage k by restoring the
binder at original outermost-first position n-(k+1): an existential wraps the
previous stage, and a universal replaces its fresh name by the original variable
before wrapping it. Every Skolem term uses the original ordered existential
dependencies, allocation and naming table. The source stages are 0 through n;
the total Nat-indexed function retains stage n at larger indices. -/
@[blueprint "chap7__definition_7_5_4" (main := true)]
def sigmaMatrix {L : Language} {Γ : List (FormulaN L)}
    (sd : SkolemData L Γ) (j : Fin Γ.length)
    (sigma : Substitution (validitySkolemLanguage Γ))
    {terms : List (Term (validitySkolemLanguage Γ))}
    (names : FreshTermNames Γ terms)
    (hCover : SigmaMatrixNamesCover sd j sigma names) (i : Nat) :
    FormulaN (validitySkolemLanguage Γ) :=
  let prefix_ := prenexPrefix (Γ.get j)
  let mat := liftValidityFormula Γ (prenexMatrix (Γ.get j))
  let base := (List.ofFn (fun p : Fin prefix_.length => p)).foldl (fun body p =>
    match h : (prefix_.get p).1 with
    | .universal =>
      let t := Substitution.applyTerm sigma (skolemTerm sd ⟨j, p, h⟩)
      let v := newVariable names t (hCover t (sigmaMatrixTerm_mem sd j sigma p h))
      formulaSubstN body (.var v) (prefix_.get p).2
    | .existential => body) mat
  let rec stage : Nat → FormulaN (validitySkolemLanguage Γ)
    | 0 => base
    | k + 1 =>
      let previous := stage k
      if hk : k < prefix_.length then
        let p : Fin prefix_.length := ⟨prefix_.length - (k + 1), by omega⟩
        match h : (prefix_.get p).1 with
        | .universal =>
          let t := Substitution.applyTerm sigma (skolemTerm sd ⟨j, p, h⟩)
          let v := newVariable names t (hCover t (sigmaMatrixTerm_mem sd j sigma p h))
          .all (prefix_.get p).2 (formulaSubstN previous (.var (prefix_.get p).2) v)
        | .existential => .ex (prefix_.get p).2 previous
      else previous
  stage i

end LCS.Herbrand.HerbrandTheorem
