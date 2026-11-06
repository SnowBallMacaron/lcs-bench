import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.SeparatingPairs
import Attach
import LCS.FOResolution.Method.Resolvents.ProofsStamp

section
namespace LCS.FOResolution.ClauseForm.FOAtomCore
open LCS.FirstOrder.Basic
open LCS.FOResolution.Unification

/-- Apply a simultaneous first-order substitution to an atom. -/
@[blueprint "chap8__definition_8_5_2"]
def subst {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L) (atom : FOAtom L hNoEq) : FOAtom L hNoEq :=
  atom.mapTerms (fun t => termSubstAll t sigma)

end LCS.FOResolution.ClauseForm.FOAtomCore

namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

/-- Definition 8.5.2 (companion): Apply a substitution to a first-order
    literal by applying it to the underlying atomic formula. -/
@[blueprint "chap8__definition_8_5_2"]
def substLit {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L)
    (lit : FOLiteral L hNoEq) : FOLiteral L hNoEq :=
  match lit with
  | .pos B => .pos (B.subst (hNoEq := by first | exact hNoEq | done) sigma)
  | .neg B => .neg (B.subst (hNoEq := by first | exact hNoEq | done) sigma)
where
  /-- Apply a substitution to all terms in a formula using the
      homomorphic extension termSubstAll. -/
  substFormula (sigma : Nat → Term L) : FormulaN L → FormulaN L
    | .predN P args => .predN P (fun i => termSubstAll (args i) sigma)
    | .eq_ hL t1 t2 => .eq_ hL (termSubstAll t1 sigma) (termSubstAll t2 sigma)
    | .neg A => .neg (substFormula sigma A)
    | .conj A B => .conj (substFormula sigma A) (substFormula sigma B)
    | .disj A B => .disj (substFormula sigma A) (substFormula sigma B)
    | .impl A B => .impl (substFormula sigma A) (substFormula sigma B)
    | .all i A => .all i (substFormula sigma A)
    | .ex i A => .ex i (substFormula sigma A)

-- retained: used by LCS.FOResolution.Method.Soundness.SubstitutionSemantics, LCS.SLD.LogicProgramming.Correctness.AnswerSubstitutions
/-- Structural atom substitution commutes with the ambient-formula
    substitution retained for semantic helper lemmas. -/
theorem atomSubst_toFormula {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L)
    (atom : FOAtom L hNoEq) :
    (atom.subst (hNoEq := by first | exact hNoEq | done) sigma).toFormula =
      substLit.substFormula sigma atom.toFormula := by
  cases atom <;> rfl

/-- Definition 8.5.2 (companion): Apply a substitution to a list of
    literals by mapping substLit over the list. -/
@[blueprint "chap8__definition_8_5_2"]
def substLits {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L)
    (lits : List (FOLiteral L hNoEq)) : List (FOLiteral L hNoEq) :=
  lits.map (substLit (hNoEq := by first | exact hNoEq | done) sigma)

/-- Definition 8.5.2 (companion): Predicate that two sets of literals
    have opposite sign: if A' is positive then B' is negative, and vice
    versa. -/
@[blueprint "chap8__definition_8_5_2"]
def LitSetOppositeSign {L : Language} (hNoEq : L.withoutEquality)
    (A' B' : List (FOLiteral L hNoEq)) : Prop :=
  (LitSetPositive (hNoEq := by first | exact hNoEq | done) A' ∧ LitSetNegative (hNoEq := by first | exact hNoEq | done) B') ∨
  (LitSetNegative (hNoEq := by first | exact hNoEq | done) A' ∧ LitSetPositive (hNoEq := by first | exact hNoEq | done) B')

/-- Definition 8.5.2 (companion): Subset relation on lists (treated as
    sets): every element of the first list is a member of the second. -/
@[blueprint "chap8__definition_8_5_2"]
def IsSublist {a : Type} (sub full : List a) : Prop :=
  ∀ x, x ∈ sub → x ∈ full

/-- Definition 8.5.2 (companion): List difference: elements of the first
    list that are not members of the second list. Requires DecidableEq. -/
@[blueprint "chap8__definition_8_5_2"]
def listDiff {a : Type} [DecidableEq a]
    (xs ys : List a) : List a :=
  xs.filter (fun x => !ys.contains x)

/-- Definition 8.5.2 (companion): All literals in a list share the same
    predicate symbol P. This captures the textbook requirement that a
    resolution step resolves on a single predicate. Each literal must be
    either pos (predN P args) or neg (predN P args) for the SAME P. -/
@[blueprint "chap8__definition_8_5_2"]
def LitSetSamePred {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) : Prop :=
  ∃ (P : L.predSymbols),
    ∀ lit, lit ∈ lits → ∃ args, lit.formula = FormulaN.predN P args

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The unsigned atomic payload of a literal. -/
def literalAtom {L : Language} (hNoEq : L.withoutEquality) : FOLiteral L hNoEq → FOAtom L hNoEq
  | .pos atom | .neg atom => atom

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Per-position equations between two applications of the same predicate.
    Predicate mismatches and equality atoms are rejected visibly with `none`;
    resolution without equality only admits the successful predicate case. -/
noncomputable def atomUnifPairs? {L : Language} (hNoEq : L.withoutEquality)
    (reference atom : FOAtom L hNoEq) : Option (List (Term L × Term L)) := by
  classical
  exact match reference, atom with
    | .predN P referenceArgs, .predN Q args =>
        if h : P = Q then
          some (List.ofFn (fun i =>
            (referenceArgs i, args (i.cast (congrArg L.predArity h)))))
        else
          none
    | _, _ => none

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Build the equation system relating every remaining literal to one
    fixed reference literal, position by position. -/
noncomputable def litSetUnifPairsAgainst {L : Language} (hNoEq : L.withoutEquality)
    (reference : FOLiteral L hNoEq) :
    List (FOLiteral L hNoEq) → Option (List (Term L × Term L))
  | [] => some []
  | lit :: rest =>
      match atomUnifPairs? (hNoEq := by first | exact hNoEq | done) (literalAtom (hNoEq := by first | exact hNoEq | done) reference) (literalAtom (hNoEq := by first | exact hNoEq | done) lit),
          litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) reference rest with
      | some pairs, some restPairs => some (pairs ++ restPairs)
      | _, _ => none

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Extract the faithful pairwise unification problem for a nonempty literal
    set. The first atom is the common reference; a malformed or empty set is
    rejected with `none`. -/
noncomputable def litSetUnifPairs {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) : Option (List (Term L × Term L)) :=
  match lits with
  | [] => none
  | reference :: rest =>
      FOAtomCore.casesOn (literalAtom hNoEq reference)
        (fun _ _ => litSetUnifPairsAgainst hNoEq reference rest)
        (fun _ _ _ => none)

-- retained: used by LCS.SLD.FirstOrder.HornClauses, LCS.SLD.LogicProgramming.Correctness.RefutationExamples
/-- Equation extraction for two applications of the same predicate is exactly
    the list of corresponding argument pairs. -/
theorem atomUnifPairs?_predN_same {L : Language} (hNoEq : L.withoutEquality)
    (P : L.predSymbols)
    (referenceArgs args : Fin (L.predArity P) → Term L) :
    atomUnifPairs? (hNoEq := by first | exact hNoEq | done) (.predN P referenceArgs) (.predN P args) =
      some (List.ofFn (fun i => (referenceArgs i, args i))) := by
  classical
  simp [atomUnifPairs?]

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- If the generated equation system is pairwise unified, every atom in the
    tail agrees position-by-position with the fixed reference atom. -/
theorem litSetUnifPairsAgainst_unifies_reference {L : Language} (hNoEq : L.withoutEquality)
    (sigma : Nat → Term L)
    (reference : FOLiteral L hNoEq)
    {rest : List (FOLiteral L hNoEq)}
    {pairs : List (Term L × Term L)}
    (hPairs : litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) reference rest = some pairs)
    (hUnif : IsPairwiseUnifier sigma pairs)
    {P : L.predSymbols}
    {referenceArgs : Fin (L.predArity P) → Term L}
    (hReference : literalAtom (hNoEq := by first | exact hNoEq | done) reference = .predN P referenceArgs)
    {lit : FOLiteral L hNoEq}
    {args : Fin (L.predArity P) → Term L}
    (hMem : lit ∈ rest)
    (hLit : literalAtom (hNoEq := by first | exact hNoEq | done) lit = .predN P args) :
    ∀ i, termSubstAll (referenceArgs i) sigma =
      termSubstAll (args i) sigma := by
  induction rest generalizing pairs with
  | nil =>
      exact (List.not_mem_nil hMem).elim
  | cons head tail ih =>
      simp only [litSetUnifPairsAgainst] at hPairs
      cases hHeadPairs :
          atomUnifPairs? (hNoEq := by first | exact hNoEq | done) (literalAtom (hNoEq := by first | exact hNoEq | done) reference) (literalAtom (hNoEq := by first | exact hNoEq | done) head) with
      | none =>
          simp [hHeadPairs] at hPairs
      | some headPairs =>
          cases hTailPairs :
              litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) reference tail with
          | none =>
              simp [hHeadPairs, hTailPairs] at hPairs
          | some tailPairs =>
              simp [hHeadPairs, hTailPairs] at hPairs
              subst pairs
              rcases List.mem_cons.mp hMem with hMemHead | hMemTail
              · subst lit
                have hHeadEq :
                    atomUnifPairs? (hNoEq := by first | exact hNoEq | done) (literalAtom (hNoEq := by first | exact hNoEq | done) reference) (literalAtom (hNoEq := by first | exact hNoEq | done) head) =
                      some (List.ofFn (fun i =>
                        (referenceArgs i, args i))) := by
                  rw [hReference, hLit]
                  exact atomUnifPairs?_predN_same (hNoEq := by first | exact hNoEq | done) P referenceArgs args
                rw [hHeadEq] at hHeadPairs
                injection hHeadPairs with hPairsEq
                subst headPairs
                intro i
                exact hUnif (referenceArgs i, args i)
                  (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
              · apply ih hTailPairs
                  (fun p hp => hUnif p (List.mem_append_right _ hp))
                  hMemTail

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting, LCS.FOResolution.Method.Soundness.ResolventValidity
/-- A unifier of the generated reference equation system makes any two
    predicate atoms in the source list agree at each argument position. -/
theorem litSetUnifPairs_unifies_position {L : Language} (hNoEq : L.withoutEquality)
    (sigma : Nat → Term L)
    {lits : List (FOLiteral L hNoEq)}
    {pairs : List (Term L × Term L)}
    (hPairs : litSetUnifPairs (hNoEq := hNoEq) lits = some pairs)
    (hUnif : IsPairwiseUnifier sigma pairs)
    {P : L.predSymbols}
    (hPred : ∀ lit, lit ∈ lits →
      ∃ args : Fin (L.predArity P) → Term L,
        literalAtom (hNoEq := by first | exact hNoEq | done) lit = .predN P args)
    {lit₁ lit₂ : FOLiteral L hNoEq}
    (hMem₁ : lit₁ ∈ lits)
    (hMem₂ : lit₂ ∈ lits)
    {args₁ args₂ : Fin (L.predArity P) → Term L}
    (hLit₁ : literalAtom (hNoEq := by first | exact hNoEq | done) lit₁ = .predN P args₁)
    (hLit₂ : literalAtom (hNoEq := by first | exact hNoEq | done) lit₂ = .predN P args₂) :
    ∀ i, termSubstAll (args₁ i) sigma =
      termSubstAll (args₂ i) sigma := by
  cases lits with
  | nil =>
      exact (List.not_mem_nil hMem₁).elim
  | cons reference rest =>
      obtain ⟨referenceArgs, hReference⟩ :=
        hPred reference List.mem_cons_self
      simp [litSetUnifPairs, hReference] at hPairs
      have toReference :
          ∀ {lit : FOLiteral L hNoEq},
            lit ∈ reference :: rest →
            ∀ {args : Fin (L.predArity P) → Term L},
              literalAtom (hNoEq := by first | exact hNoEq | done) lit = .predN P args →
              ∀ i, termSubstAll (referenceArgs i) sigma =
                termSubstAll (args i) sigma := by
        intro lit hMem args hLit
        rcases List.mem_cons.mp hMem with rfl | hMemRest
        · have hArgs : referenceArgs = args := by
            rw [hReference] at hLit
            exact eq_of_heq (FOAtomCore.predN.inj hLit).2
          subst args
          intro i
          rfl
        · exact litSetUnifPairsAgainst_unifies_reference (hNoEq := by first | exact hNoEq | done)
            sigma reference hPairs hUnif hReference hMemRest hLit
      intro i
      exact (toReference hMem₁ hLit₁ i).symm.trans
        (toReference hMem₂ hLit₂ i)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Definition 8.5.2 with all resolution witnesses fixed explicitly.
    The selected literals yield one per-position equation system, and the
    stored substitution must be an MGU of exactly that system. The result
    has the same literal members as the substituted union of remainders;
    list order and repeated literals do not constrain the clause. -/
@[blueprint "chap8__example_8_5_1"]
def IsResolventVia {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (C A B : FOClause L hNoEq)
    (A' B' : List (FOLiteral L hNoEq))
    (rho rho' sigma : Nat → Term L) : Prop :=
  IsSublist A' A ∧
  IsSublist B' B ∧
  A' ≠ [] ∧
  B' ≠ [] ∧
  LitSetSameSign (hNoEq := by first | exact hNoEq | done) A' ∧
  LitSetOppositeSign (hNoEq := by first | exact hNoEq | done) A' B' ∧
  LitSetSamePred (hNoEq := by first | exact hNoEq | done) (A' ++ LitSetConjugate (hNoEq := by first | exact hNoEq | done) B') ∧
  IsSeparatingPair (hNoEq := by first | exact hNoEq | done) rho rho' A B ∧
  (∃ pairs : List (Term L × Term L),
    litSetUnifPairs (hNoEq := by first | exact hNoEq | done)
      (LitSetAbs (hNoEq := by first | exact hNoEq | done)
        (substLits (hNoEq := by first | exact hNoEq | done) rho A' ++ substLits (hNoEq := by first | exact hNoEq | done) rho' (LitSetConjugate (hNoEq := by first | exact hNoEq | done) B'))) =
      some pairs ∧
    IsPairwiseUnifier sigma pairs ∧
    IsPairwiseMGU sigma pairs) ∧
  ∀ lit, lit ∈ C ↔
    lit ∈ substLits (hNoEq := by first | exact hNoEq | done) sigma
      (substLits (hNoEq := by first | exact hNoEq | done) rho (listDiff A A') ++
       substLits (hNoEq := by first | exact hNoEq | done) rho' (listDiff B B'))

/-- Definition 8.5.2: C is a resolvent of A and B via opposite-sign
    subsets A'/B', a separating pair, and an mgu sigma. Clause lists
    represent finite literal sets; the result is compared by membership. -/
@[blueprint "chap8__definition_8_5_2" (main := true)]
def IsResolvent {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (C A B : FOClause L hNoEq) : Prop :=
  ∃ (A' : List (FOLiteral L hNoEq))
    (B' : List (FOLiteral L hNoEq))
    (rho rho' sigma : Nat → Term L),
    IsResolventVia (hNoEq := by first | exact hNoEq | done) C A B A' B' rho rho' sigma

end LCS.FOResolution.Method
end
