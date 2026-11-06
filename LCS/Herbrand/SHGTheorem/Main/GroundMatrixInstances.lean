import LCS.Item
import LCS.Util
import LCS.Herbrand.SHGTheorem
import LCS.Herbrand.SHGTheorem.Herbrand
import Attach
import LCS.Herbrand.SHGTheorem.Main.GroundMatrixInstances.ProofsStamp

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
-- Corollary 7.6.1 (companion def): applyGroundSubstitution
-- ===================================================================

/-- Corollary 7.6.1 (companion def): Applies a list of (variable, closed-term) pairs as a sequential substitution to a formula M. Each pair (xᵢ, tᵢ) contributes a single-variable substitution M[tᵢ/xᵢ], composed left-to-right. When applied to the matrix of a prenex ∀-formula with the closed terms matching the bound variables of the universal prefix, this produces a single ground substitution instance of the matrix. -/
@[blueprint "chap7__theorem_7_6_1"]
def applyGroundSubstitution {L : Language}
    (M : FormulaN L) (substs : List (Nat × Term L)) : FormulaN L :=
  substs.foldl (fun acc p => formulaSubstN acc p.2 p.1) M

-- retained: used by LCS.Herbrand.SHGTheorem.Main.GroundMatrix
/-- Exact ordered substitution of every universal prefix binder by a
closed term closes the matrix of a closed universal-prenex source.
Distinct bindings ensure that stripping the current binder commutes
with substitution into the remaining prefix. -/
theorem applyGroundSubstitution_isClosed_of_fullPrefix
    {L : Language} (source : FormulaN L)
    (substitutions : List (Nat × Term L))
    (hComplete :
      substitutions.map Prod.fst =
        (prenexPrefix source).map Prod.snd)
    (hTermsClosed :
      ∀ p ∈ substitutions, Term.isClosed p.2)
    (hSourceClosed : FormulaN.isClosed source)
    (hUniversal : UniversalPrenexFormula source)
    (hDistinct : distinctQuantifierBindings source) :
    FormulaN.isClosed
      (applyGroundSubstitution
        (prenexMatrix source) substitutions) := by
  have hClose :
      ∀ (m : Nat) (current : FormulaN L)
        (remaining : List (Nat × Term L)),
        formulaQuantCount current = m →
        remaining.map Prod.fst =
          (prenexPrefix current).map Prod.snd →
        (∀ p ∈ remaining, Term.isClosed p.2) →
        FormulaN.isClosed current →
        UniversalPrenexFormula current →
        distinctQuantifierBindings current →
        FormulaN.isClosed
          (applyGroundSubstitution
            (prenexMatrix current) remaining) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro current remaining hCount hKeys hClosedTerms
        hCurrentClosed hCurrentUniversal hCurrentDistinct
      cases current with
      | predN P ts =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | eq_ hEq t₁ t₂ =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | neg C =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | conj C D =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | disj C D =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | impl C D =>
        cases remaining with
        | nil =>
          simpa [prenexMatrix, applyGroundSubstitution] using
            hCurrentClosed
        | cons _ _ =>
          simp [prenexPrefix] at hKeys
      | all x C =>
        cases remaining with
        | nil =>
          simp [prenexPrefix] at hKeys
        | cons head rest =>
          obtain ⟨key, term⟩ := head
          simp only [List.map_cons, Prod.fst, prenexPrefix,
            Prod.snd] at hKeys
          have hKey : key = x :=
            (List.cons.inj hKeys).1
          have hRestKeys :
              rest.map Prod.fst =
                (prenexPrefix C).map Prod.snd :=
            (List.cons.inj hKeys).2
          subst key
          have hTermClosed : Term.isClosed term :=
            hClosedTerms (x, term) List.mem_cons_self
          have hRestClosed :
              ∀ p ∈ rest, Term.isClosed p.2 := by
            intro p hp
            exact hClosedTerms p
              (List.mem_cons.mpr (Or.inr hp))
          have hSubClosed :
              FormulaN.isClosed
                (formulaSubstN C term x) := by
            have hSourceFV :
                formulaFVN (FormulaN.all x C) =
                  (∅ : Set Nat) :=
              hCurrentClosed
            have hTermFV :
                termFV term = (∅ : Set Nat) :=
              hTermClosed
            unfold FormulaN.isClosed
            funext y
            apply propext
            constructor
            · intro hy
              rcases
                  LCS.FirstOrder.Gentzen.Hintikka.formulaFVN_formulaSubstN
                    C term x y hy with
                ⟨hyC, hyNe⟩ | hyTerm
              · have hySource :
                    y ∈ formulaFVN
                      (FormulaN.all x C) :=
                  ⟨hyC, hyNe⟩
                rw [hSourceFV] at hySource
                exact hySource.elim
              · rw [hTermFV] at hyTerm
                exact hyTerm.elim
            · intro hy
              exact hy.elim
          have hBodyUniversal :
              UniversalPrenexFormula C :=
            universalPrenexFormula_body_of_all
              C x hCurrentUniversal
          have hSubUniversal :
              UniversalPrenexFormula
                (formulaSubstN C term x) :=
            universalPrenexFormula_formulaSubstN
              C term x hBodyUniversal
          have hSubDistinct :
              distinctQuantifierBindings
                (formulaSubstN C term x) :=
            Herbrand.distinctQuantifierBindings_of_formulaSubstN
              C term x hCurrentDistinct.1
          have hSubCount :
              formulaQuantCount
                  (formulaSubstN C term x) =
                formulaQuantCount C :=
            formulaSubst_quantCount C term x
          have hSubLt :
              formulaQuantCount
                  (formulaSubstN C term x) < m := by
            rw [hSubCount]
            simp [formulaQuantCount] at hCount
            omega
          have hRestKeysSub :
              rest.map Prod.fst =
                (prenexPrefix
                  (formulaSubstN C term x)).map Prod.snd := by
            rw [prenexPrefix_formulaSubstN]
            exact hRestKeys
          have hClosedRest :=
            ih
              (formulaQuantCount
                (formulaSubstN C term x))
              hSubLt (formulaSubstN C term x) rest rfl
              hRestKeysSub hRestClosed hSubClosed
              hSubUniversal hSubDistinct
          have hMatrix :
              prenexMatrix (formulaSubstN C term x) =
                formulaSubstN (prenexMatrix C) term x :=
            Herbrand.prenexMatrix_formulaSubstN_of_not_bv
              C term x hCurrentDistinct.2
          rw [hMatrix] at hClosedRest
          simpa only [prenexMatrix, applyGroundSubstitution,
            List.foldl_cons] using hClosedRest
      | ex x C =>
        have hImpossible :
            QuantifierKind.existential =
              QuantifierKind.universal :=
          hCurrentUniversal.2
            (QuantifierKind.existential, x)
            (by simp [prenexPrefix])
        cases hImpossible
  exact
    hClose (formulaQuantCount source) source substitutions rfl
      hComplete hTermsClosed hSourceClosed hUniversal hDistinct

-- ===================================================================
-- Corollary 7.6.1 (companion structure): GroundMatrixInstance
-- ===================================================================

/-- A proof-coupled ground instance of the matrix of `B`.

The substitution keys cover the prenex prefix exactly, in
outermost-to-innermost order. Every replacement term is closed, and the
computed matrix instance is recorded as closed. The latter condition also
rejects residual free variables which do not belong to the prefix. -/
@[blueprint "chap7__theorem_7_6_1"]
structure GroundMatrixInstance {L : Language} (B : FormulaN L) where
  substitution : List (Nat × Term L)
  complete :
    substitution.map Prod.fst =
      (LCS.Herbrand.PrenexForm.prenexPrefix B).map Prod.snd
  termsClosed :
    ∀ p ∈ substitution, Term.isClosed p.2
  leafClosed :
    FormulaN.isClosed
      (applyGroundSubstitution
        (LCS.Herbrand.PrenexForm.prenexMatrix B)
        substitution)

namespace GroundMatrixInstance

/-- The formula carried by one complete ground matrix instance. -/
@[blueprint "chap7__theorem_7_6_1"]
def toFormula {L : Language} {B : FormulaN L}
    (g : GroundMatrixInstance B) : FormulaN L :=
  applyGroundSubstitution
    (LCS.Herbrand.PrenexForm.prenexMatrix B)
    g.substitution

end GroundMatrixInstance

/-- Proof-relevant flattening of a binary conjunction into its ordered
leaves. The `leaf` constructor may stop at any formula, so a conjunction
which is itself one matrix instance is not split accidentally. The `conj`
constructor preserves order and multiplicity while allowing either binary
bracketing of the same leaf list. -/
@[blueprint "chap7__theorem_7_6_1"]
inductive ConjunctionFlattening {L : Language} :
    FormulaN L → List (FormulaN L) → Prop where
  | leaf (A : FormulaN L) :
      ConjunctionFlattening A [A]
  | conj {A B : FormulaN L} {as bs : List (FormulaN L)} :
      ConjunctionFlattening A as →
      ConjunctionFlattening B bs →
      ConjunctionFlattening (.conj A B) (as ++ bs)

namespace ConjunctionFlattening

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Evaluation of a represented conjunction is equivalent to evaluation
of every leaf in its ordered list. -/
theorem formulaEvalN_iff_all_leaves {L : Language}
    {F : FormulaN L} {leaves : List (FormulaN L)}
    (flattening : ConjunctionFlattening F leaves)
    (M : Structure L) (s : Assignment M) :
    formulaEvalN M F s ↔
      ∀ A ∈ leaves, formulaEvalN M A s := by
  induction flattening with
  | leaf A =>
    constructor
    · intro hA C hC
      simp only [List.mem_singleton] at hC
      subst C
      exact hA
    · intro hAll
      exact hAll A List.mem_cons_self
  | @conj A B as bs flatteningA flatteningB evalA evalB =>
    simp only [formulaEvalN]
    constructor
    · rintro ⟨hA, hB⟩ C hC
      rcases List.mem_append.mp hC with hCA | hCB
      · exact (evalA.mp hA) C hCA
      · exact (evalB.mp hB) C hCB
    · intro hAll
      exact
        ⟨evalA.mpr (fun C hC =>
            hAll C (List.mem_append.mpr (Or.inl hC))),
         evalB.mpr (fun C hC =>
            hAll C (List.mem_append.mpr (Or.inr hC)))⟩

end ConjunctionFlattening

/-- Corollary 7.6.1 (companion def): `F` is a nonempty finite
conjunction of complete, ordered, closed ground substitution instances of
the matrix of the universal-prenex NNF formula `B`. Distinct quantifier
bindings make the sequential prefix positions unambiguous. The
proof-relevant flattening preserves leaf order and multiplicity but does
not impose one global conjunction association. -/
@[blueprint "chap7__theorem_7_6_1"]
def isFiniteGroundConjunctionOfMatrix {L : Language}
    (F : FormulaN L) (B : FormulaN L) : Prop :=
  LCS.Herbrand.NNFHauptsatz.Theorem.UniversalPrenexFormula B ∧
  FormulaN.isNNF B ∧
  LCS.FirstOrder.Semantics.Subformulae.distinctQuantifierBindings B ∧
  ∃ instances : List (GroundMatrixInstance B),
    ConjunctionFlattening F
      (instances.map GroundMatrixInstance.toFormula)

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

end GroundMatrixCarrierRegression
end LCS.Herbrand.SHGTheorem.Main
end
