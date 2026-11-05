import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import Attach
import LCS.FOResolution.Method.ResolutionTrees.ProofsStamp

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

/-- Definition 8.5.3: A first-order resolution tree, encoding a DAG for
    first-order clauses with separating pair + mgu at each resolve node. -/
@[blueprint "chap8__definition_8_5_3" (main := true)]
inductive FOResolutionTree (L : Language) (hNoEq : L.withoutEquality) : Type where
  /-- A leaf node labeled with a clause from the input set S -/
  | axiom_ : FOClause L hNoEq → FOResolutionTree L hNoEq
  /-- An internal resolution step node with two subtrees, the literal
      subsets A' (resolvedA) and B' (resolvedB) that are resolved on,
      a separating pair (rho, rho') of substitutions, and a most
      general unifier sigma. The resolvent clause is computed as
      sigma(rho(label(T1) - resolvedA) ++ rho'(label(T2) - resolvedB)). -/
  | resolve :
      FOResolutionTree L hNoEq →
      FOResolutionTree L hNoEq →
      (resolvedA : List (FOLiteral L hNoEq)) →
      (resolvedB : List (FOLiteral L hNoEq)) →
      (rho : Nat → Term L) →
      (rho' : Nat → Term L) →
      (sigma : Nat → Term L) →
      FOResolutionTree L hNoEq

-- ===================================================================
-- Definition 8.5.3 (companion type): First-order resolution DAG
-- ===================================================================

/-- Definition 8.5.3: A first-order resolution DAG is a finite set
    (represented as a list) of resolution trees. -/
@[blueprint "chap8__definition_8_5_3" (main := true)]
abbrev FOResolutionDAG (L : Language) (hNoEq : L.withoutEquality) : Type :=
  List (FOResolutionTree L hNoEq)

-- ===================================================================
-- Definition 8.5.1: Separating pair of substitutions
-- ===================================================================

/-- Definition 8.5.1 (companion): The set of free variables occurring in
    a clause: the union of the variable sets of all literals in the
    clause. -/
@[blueprint "chap8__definition_8_5_1"]
def clauseFV {L : Language} (hNoEq : L.withoutEquality) (c : FOClause L hNoEq) : Set Nat :=
  fun m => ∃ lit, lit ∈ c ∧ FOLiteral.vars hNoEq lit m

/-- Definition 8.5.1 (companion): Predicate that a substitution maps
    every variable in a given set to a variable (not a compound term). -/
@[blueprint "chap8__definition_8_5_1"]
def substIsVarOnSet {L : Language} (sigma : Nat → Term L)
    (S : Set Nat) : Prop :=
  ∀ x, S x → ∃ y, sigma x = Term.var y

/-- Definition 8.5.1 (companion): Predicate that a substitution is
    injective on a given set of variables. -/
@[blueprint "chap8__definition_8_5_1"]
def substInjectiveOnSet {L : Language} (sigma : Nat → Term L)
    (S : Set Nat) : Prop :=
  ∀ x y, S x → S y → sigma x = sigma y → x = y

/-- Definition 8.5.1 (companion): The range of a substitution restricted
    to a given set: the set of variable indices that appear as images. -/
@[blueprint "chap8__definition_8_5_1"]
def substRangeOnSet {L : Language} (sigma : Nat → Term L)
    (S : Set Nat) : Set Nat :=
  fun n => ∃ x, S x ∧ sigma x = Term.var n

/-- Definition 8.5.1: Predicate that all literals in the list are
    positive (unnegated atomic formulae). -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def LitSetPositive {L : Language} (hNoEq : L.withoutEquality) (lits : List (FOLiteral L hNoEq)) : Prop :=
  ∀ lit, lit ∈ lits → ∃ B, lit = FOLiteralCore.pos B

/-- Definition 8.5.1: Predicate that all literals in the list are
    negative (negations of atomic formulae). -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def LitSetNegative {L : Language} (hNoEq : L.withoutEquality) (lits : List (FOLiteral L hNoEq)) : Prop :=
  ∀ lit, lit ∈ lits → ∃ B, lit = FOLiteralCore.neg B

/-- Definition 8.5.1: An equality-free literal set has the same sign
    when all its literals are positive or all are negative. The empty
    set satisfies both alternatives; admission of a resolution step
    separately requires nonempty pivot sets. -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def LitSetSameSign {L : Language} (hNoEq : L.withoutEquality) (lits : List (FOLiteral L hNoEq)) : Prop :=
  LitSetPositive (hNoEq := by first | exact hNoEq | done) lits ∨ LitSetNegative (hNoEq := by first | exact hNoEq | done) lits

/-- Definition 8.5.1: The conjugate of a list of literals: map
    FOLiteral.conjugate over each element. -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def LitSetConjugate {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) : List (FOLiteral L hNoEq) :=
  lits.map (FOLiteral.conjugate hNoEq)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Internal total extension of literal-set absolute value retained for
    compatibility; the canonical Definition 8.5.1 boundary is
    `LitSetAbsSameSign`. -/
@[blueprint "chap8__example_8_5_1"]
def LitSetAbs {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) : List (FOLiteral L hNoEq) :=
  match lits with
  | [] => []
  | (FOLiteralCore.pos _) :: _ => lits
  | (FOLiteralCore.neg _) :: _ => LitSetConjugate (hNoEq := by first | exact hNoEq | done) lits

/-- Definition 8.5.1: The absolute value |S| of a same-sign literal set,
    implemented by the internal total extension `LitSetAbs`. -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def LitSetAbsSameSign {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) (_hSame : LitSetSameSign (hNoEq := by first | exact hNoEq | done) lits) :
    List (FOLiteral L hNoEq) :=
  LitSetAbs (hNoEq := by first | exact hNoEq | done) lits

/-- Definition 8.5.1: A separating pair (rho, rho') for equality-free
    clauses A and A' maps each clause's variables injectively to variables,
    giving a bijection onto its local image. These two local images are
    disjoint. Each substitution fixes every variable outside its clause's
    free-variable set, so its moved support is contained in that set.
    Variables inside the set may also be fixed, as in Example 8.5.1;
    identity witnesses are allowed when the two clause-variable sets
    are already disjoint. -/
@[blueprint "chap8__definition_8_5_1" (main := true)]
def IsSeparatingPair {L : Language} (hNoEq : L.withoutEquality)
    (rho rho' : Nat → Term L)
    (A A' : FOClause L hNoEq) : Prop :=
  substIsVarOnSet rho (clauseFV (hNoEq := by first | exact hNoEq | done) A) ∧
  substIsVarOnSet rho' (clauseFV (hNoEq := by first | exact hNoEq | done) A') ∧
  substInjectiveOnSet rho (clauseFV (hNoEq := by first | exact hNoEq | done) A) ∧
  substInjectiveOnSet rho' (clauseFV (hNoEq := by first | exact hNoEq | done) A') ∧
  Set.inter (substRangeOnSet rho (clauseFV (hNoEq := by first | exact hNoEq | done) A))
            (substRangeOnSet rho' (clauseFV (hNoEq := by first | exact hNoEq | done) A')) = Set.empty ∧
  (∀ x, ¬ clauseFV (hNoEq := by first | exact hNoEq | done) A x → rho x = Term.var x) ∧
  (∀ x, ¬ clauseFV (hNoEq := by first | exact hNoEq | done) A' x → rho' x = Term.var x)

end LCS.FOResolution.Method
end

section
namespace LCS.FOResolution.ClauseForm.FOAtomCore
open LCS.FirstOrder.Basic
open LCS.FOResolution.Unification

/-- Apply a simultaneous first-order substitution to an atom. -/
@[blueprint "chap8__definition_8_5_2"]
def subst {L : Language} (hNoEq : L.withoutEquality) (sigma : Nat → Term L) (atom : FOAtom L hNoEq) : FOAtom L hNoEq :=
  atom.mapTerms (fun t => termSubstAll t sigma)

end LCS.FOResolution.ClauseForm.FOAtomCore
end

section
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

/-- Definition 8.5.2 (companion): Extract the list of terms from a list
    of positive literals for use with the unifier. Given a list of
    FOLiteral.pos applied to predN predicates, extracts the underlying
    predicate application terms. Retained as an internal proof helper;
    the resolvent contract below uses per-position equation pairs. -/
@[blueprint "chap8__definition_8_5_2"]
def litSetUnifTerms {L : Language} (hNoEq : L.withoutEquality)
    (lits : List (FOLiteral L hNoEq)) : List (Term L) :=
  lits.foldl (fun acc lit =>
    match lit with
    | .pos (.predN _ args) => acc ++ List.ofFn args
    | .neg (.predN _ args) => acc ++ List.ofFn args
    | _ => acc) []

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

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- Conversely, a position-by-position common unifier for one predicate
    produces a successful reference-pair extraction and pairwise unifier. -/
theorem litSetUnifPairsAgainst_exists_of_position_unifier {L : Language} (hNoEq : L.withoutEquality)
    (sigma : Nat → Term L)
    (source : List (FOLiteral L hNoEq))
    {P : L.predSymbols}
    (reference : FOLiteral L hNoEq)
    (rest : List (FOLiteral L hNoEq))
    (hReferenceMem : reference ∈ source)
    (hRestSub : IsSublist rest source)
    (hPred : ∀ lit, lit ∈ source →
      ∃ args : Fin (L.predArity P) → Term L,
        literalAtom (hNoEq := by first | exact hNoEq | done) lit = .predN P args)
    (hPosition :
      ∀ lit₁, lit₁ ∈ source →
      ∀ lit₂, lit₂ ∈ source →
      ∀ (args₁ args₂ : Fin (L.predArity P) → Term L),
        literalAtom (hNoEq := by first | exact hNoEq | done) lit₁ = .predN P args₁ →
        literalAtom (hNoEq := by first | exact hNoEq | done) lit₂ = .predN P args₂ →
        ∀ i, termSubstAll (args₁ i) sigma =
          termSubstAll (args₂ i) sigma) :
    ∃ pairs,
      litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) reference rest = some pairs ∧
      IsPairwiseUnifier sigma pairs := by
  obtain ⟨referenceArgs, hReference⟩ :=
    hPred reference hReferenceMem
  induction rest with
  | nil =>
      exact ⟨[], rfl, fun p hMem => (List.not_mem_nil hMem).elim⟩
  | cons head tail ih =>
      have hHeadMem : head ∈ source :=
        hRestSub head List.mem_cons_self
      obtain ⟨headArgs, hHead⟩ := hPred head hHeadMem
      have hTailSub : IsSublist tail source :=
        fun lit hMem => hRestSub lit (List.mem_cons_of_mem head hMem)
      obtain ⟨tailPairs, hTailPairs, hTailUnif⟩ :=
        ih hTailSub
      refine ⟨List.ofFn (fun i => (referenceArgs i, headArgs i)) ++
          tailPairs, ?_, ?_⟩
      · simp only [litSetUnifPairsAgainst]
        rw [hReference, hHead, atomUnifPairs?_predN_same (hNoEq := by first | exact hNoEq | done),
          hTailPairs]
      · intro pair hPairMem
        rcases List.mem_append.mp hPairMem with hHeadPair | hTailPair
        · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hHeadPair
          exact hPosition reference hReferenceMem head hHeadMem
            referenceArgs headArgs hReference hHead i
        · exact hTailUnif pair hTailPair

-- retained: used by LCS.FOResolution.Method.Completeness.Lifting
/-- A nonempty same-predicate list with a position-wise common unifier has a
    faithful extracted pair system unified by that substitution. -/
theorem litSetUnifPairs_exists_of_position_unifier {L : Language} (hNoEq : L.withoutEquality)
    (sigma : Nat → Term L)
    {lits : List (FOLiteral L hNoEq)}
    (hNonempty : lits ≠ [])
    {P : L.predSymbols}
    (hPred : ∀ lit, lit ∈ lits →
      ∃ args : Fin (L.predArity P) → Term L,
        literalAtom (hNoEq := by first | exact hNoEq | done) lit = .predN P args)
    (hPosition :
      ∀ lit₁, lit₁ ∈ lits →
      ∀ lit₂, lit₂ ∈ lits →
      ∀ (args₁ args₂ : Fin (L.predArity P) → Term L),
        literalAtom (hNoEq := by first | exact hNoEq | done) lit₁ = .predN P args₁ →
        literalAtom (hNoEq := by first | exact hNoEq | done) lit₂ = .predN P args₂ →
        ∀ i, termSubstAll (args₁ i) sigma =
          termSubstAll (args₂ i) sigma) :
    ∃ pairs,
      litSetUnifPairs (hNoEq := hNoEq) lits = some pairs ∧
      IsPairwiseUnifier sigma pairs := by
  obtain ⟨reference, rest, rfl⟩ := List.exists_cons_of_ne_nil hNonempty
  obtain ⟨referenceArgs, hReference⟩ :=
    hPred reference List.mem_cons_self
  obtain ⟨pairs, hPairs, hUnif⟩ :=
    litSetUnifPairsAgainst_exists_of_position_unifier (hNoEq := by first | exact hNoEq | done)
      sigma (reference :: rest) reference rest List.mem_cons_self
      (fun lit hMem => List.mem_cons_of_mem reference hMem)
      hPred hPosition
  refine ⟨pairs, ?_, hUnif⟩
  simp [litSetUnifPairs, hReference, hPairs]

-- ATTACH-BLOCKER: private declaration
private inductive PairwiseRegressionPred : Type where
  | nullary
  | binary
  deriving DecidableEq

-- ATTACH-BLOCKER: private declaration
private def pairwiseRegressionLanguage : Language where
  funSymbols := Empty
  funArity := Empty.elim
  constSymbols := Empty
  predSymbols := PairwiseRegressionPred
  predArity := fun
    | .nullary => 0
    | .binary => 2
  hasEquality := false

-- ATTACH-BLOCKER: private declaration
private def pairwiseRegressionNullaryAtom :
    FOAtom pairwiseRegressionLanguage rfl :=
  .predN .nullary (fun i => Fin.elim0 i)

-- ATTACH-BLOCKER: private declaration
private def pairwiseRegressionBinaryAtom :
    FOAtom pairwiseRegressionLanguage rfl :=
  .predN .binary (vec2 (.var 0) (.var 1))

-- ATTACH-BLOCKER: private declaration
private def pairwiseRegressionId :
    Nat → Term pairwiseRegressionLanguage :=
  fun n => .var n

-- ATTACH-BLOCKER: private declaration
private example :
    litSetUnifPairs (by first | rfl | done)
      [.pos pairwiseRegressionNullaryAtom,
       .pos pairwiseRegressionNullaryAtom] = some [] := by
  simp [litSetUnifPairs, litSetUnifPairsAgainst,
    pairwiseRegressionNullaryAtom, literalAtom, atomUnifPairs?,
    pairwiseRegressionLanguage] <;> rfl

-- ATTACH-BLOCKER: private declaration
private example :
    IsPairwiseMGU pairwiseRegressionId [] := by
  refine ⟨?_, ?_, ?_⟩
  · intro pair hPair
    exact (List.not_mem_nil hPair).elim
  · intro x hSupport
    exact (hSupport rfl).elim
  · intro sigmaOther _
    refine ⟨sigmaOther, ?_⟩
    intro x
    rfl

-- ATTACH-BLOCKER: private declaration
private example :
    litSetUnifPairs (by first | rfl | done)
      [.pos pairwiseRegressionBinaryAtom,
       .pos pairwiseRegressionBinaryAtom] =
      some [(.var 0, .var 0), (.var 1, .var 1)] := by
  simp [litSetUnifPairs, litSetUnifPairsAgainst,
    pairwiseRegressionBinaryAtom, literalAtom, atomUnifPairs?,
    pairwiseRegressionLanguage, vec2] <;> rfl

-- ATTACH-BLOCKER: private declaration
private example :
    IsPairwiseMGU pairwiseRegressionId
      [(.var 0, .var 0), (.var 1, .var 1)] := by
  refine ⟨?_, ?_, ?_⟩
  · intro pair hPair
    rcases List.mem_cons.mp hPair with rfl | hPair
    · rfl
    · rcases List.mem_singleton.mp hPair with rfl
      rfl
  · intro x hSupport
    exact (hSupport rfl).elim
  · intro sigmaOther _
    refine ⟨sigmaOther, ?_⟩
    intro x
    rfl

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

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
namespace FOResolutionTree

/-- Definition 8.5.3 (companion): The label (clause) at a resolution
    tree node. For a leaf, it is the clause itself. For an internal
    node, it is the resolvent clause computed from the labels of the
    two children using the separating pair and MGU. -/
@[blueprint "chap8__definition_8_5_3"]
def label {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)] :
    FOResolutionTree L hNoEq → FOClause L hNoEq
  | .axiom_ C => C
  | .resolve T1 T2 resolvedA resolvedB rho rho' sigma =>
    substLits (hNoEq := by first | exact hNoEq | done) sigma (substLits (hNoEq := by first | exact hNoEq | done) rho (listDiff (label (hNoEq := by first | exact hNoEq | done) T1) resolvedA) ++
                     substLits (hNoEq := by first | exact hNoEq | done) rho' (listDiff (label (hNoEq := by first | exact hNoEq | done) T2) resolvedB))

/-- Definition 8.5.3 (companion): Predicate that all leaves of a
    resolution tree are labeled with clauses from a given set S. -/
@[blueprint "chap8__definition_8_5_3"]
def leavesFrom {L : Language} (hNoEq : L.withoutEquality) :
    FOResolutionTree L hNoEq → (FOClause L hNoEq → Prop) → Prop
  | .axiom_ C, S => S C
  | .resolve T1 T2 _ _ _ _ _, S =>
    leavesFrom (hNoEq := by first | exact hNoEq | done) T1 S ∧ leavesFrom (hNoEq := by first | exact hNoEq | done) T2 S

/-- Definition 8.5.3 (companion): Predicate that a resolution tree is
    well-formed: every internal node represents a valid resolution step
    (the label is a resolvent of the two children's labels via the given
    separating pair and MGU). -/
@[blueprint "chap8__definition_8_5_3"]
def isWellFormed {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)] :
    FOResolutionTree L hNoEq → Prop
  | .axiom_ _ => True
  | .resolve T1 T2 resolvedA resolvedB rho rho' sigma =>
    isWellFormed (hNoEq := by first | exact hNoEq | done) T1 ∧
    isWellFormed (hNoEq := by first | exact hNoEq | done) T2 ∧
    IsResolventVia (hNoEq := by first | exact hNoEq | done)
      (label (hNoEq := by first | exact hNoEq | done) (.resolve T1 T2 resolvedA resolvedB rho rho' sigma))
      (label (hNoEq := by first | exact hNoEq | done) T1) (label (hNoEq := by first | exact hNoEq | done) T2) resolvedA resolvedB rho rho' sigma

end FOResolutionTree
end LCS.FOResolution.Method
end

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
namespace FOResolutionDAG

/-- Definition 8.5.3 (companion): A resolution DAG D is a resolution DAG
    for a set of clauses S iff D is nonempty, every tree in D has leaves
    from S, and every tree in D is well-formed. -/
@[blueprint "chap8__definition_8_5_3"]
def isResolutionDAGFor {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (D : FOResolutionDAG L hNoEq) (S : FOClause L hNoEq → Prop) : Prop :=
  D ≠ [] ∧
  (∀ T, T ∈ D → T.leavesFrom (hNoEq := by first | exact hNoEq | done) S) ∧
  (∀ T, T ∈ D → T.isWellFormed (hNoEq := by first | exact hNoEq | done))

/-- Definition 8.5.3: A resolution DAG is a resolution refutation iff
    it consists of a single tree whose root is the empty clause. -/
@[blueprint "chap8__definition_8_5_3" (main := true)]
def isResolutionRefutation {L : Language} (hNoEq : L.withoutEquality) [DecidableEq (FOLiteral L hNoEq)]
    (D : FOResolutionDAG L hNoEq) (S : FOClause L hNoEq → Prop) : Prop :=
  ∃ T : FOResolutionTree L hNoEq,
      D = [T] ∧
      T.leavesFrom (hNoEq := by first | exact hNoEq | done) S ∧
      T.isWellFormed (hNoEq := by first | exact hNoEq | done) ∧
      T.label (hNoEq := by first | exact hNoEq | done) = []

end FOResolutionDAG
end LCS.FOResolution.Method
end

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A conservative extension of `L` with exactly one new constant symbol.
    Function symbols, predicate symbols, their arities, and the equality flag
    are unchanged.  This supplies a closed term for the ground phase of
    first-order resolution completeness even when `L` has no ground terms. -/
@[blueprint "chap8__lemma_8_5_4"]
def FreshGroundLanguage (L : Language) : Language where
  funSymbols := L.funSymbols
  funArity := L.funArity
  constSymbols := L.constSymbols ⊕ Unit
  predSymbols := L.predSymbols
  predArity := L.predArity
  hasEquality := L.hasEquality

end LCS.FOResolution.Method
end

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
namespace FreshGroundLanguage

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The unique constant symbol added by `FreshGroundLanguage`. -/
def freshConstantSymbol {L : Language} :
    (FreshGroundLanguage L).constSymbols :=
  Sum.inr ()

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The distinguished closed term supplied by the fresh extension. -/
def seed {L : Language} : Term (FreshGroundLanguage L) :=
  .const freshConstantSymbol













-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Adding the fresh constant neither adds nor removes equality. -/
@[blueprint "chap8__lemma_8_5_4"]
theorem withoutEquality_iff (L : Language) :
    (FreshGroundLanguage L).withoutEquality ↔ L.withoutEquality

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Structural embedding of base-language terms into the fresh extension. -/
def liftTerm {L : Language} :
    Term L → Term (FreshGroundLanguage L)
  | .var x => .var x
  | .const c => .const (Sum.inl c)
  | .func f args => .func f (fun i => liftTerm (args i))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Structural embedding of base-language atoms into the fresh extension. -/
def liftAtom {L : Language} (hNoEq : L.withoutEquality) :
    FOAtom L hNoEq → FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)
  | .predN P args => .predN P (fun i => liftTerm (args i))
  | .eq_ hL lhs rhs => .eq_ hL (liftTerm lhs) (liftTerm rhs)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Structural embedding of base-language literals into the fresh extension. -/
def liftLiteral {L : Language} (hNoEq : L.withoutEquality) :
    FOLiteral L hNoEq → FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)
  | .pos atom => .pos (liftAtom (hNoEq := by first | exact hNoEq | done) atom)
  | .neg atom => .neg (liftAtom (hNoEq := by first | exact hNoEq | done) atom)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pointwise embedding of a base-language clause. -/
@[blueprint "chap8__lemma_8_5_4"]
def liftClause {L : Language} (hNoEq : L.withoutEquality) (C : FOClause L hNoEq) :
    FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) :=
  C.map (liftLiteral (hNoEq := by first | exact hNoEq | done))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pointwise embedding of a base-language substitution. -/
def liftSubst {L : Language} (sigma : Nat → Term L) :
    Nat → Term (FreshGroundLanguage L) :=
  fun x => liftTerm (sigma x)

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- A term in the extension uses only original constants.  Since function
    symbols are unchanged, this is exactly the image predicate for `liftTerm`. -/
inductive IsOriginalTerm {L : Language} :
    Term (FreshGroundLanguage L) → Prop where
  | var (x : Nat) : IsOriginalTerm (.var x)
  | const (c : L.constSymbols) :
      IsOriginalTerm (.const (Sum.inl c))
  | func (f : L.funSymbols)
      (args : Fin (L.funArity f) → Term (FreshGroundLanguage L))
      (hargs : ∀ i, IsOriginalTerm (args i)) :
      IsOriginalTerm (.func f args)

-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- Total structural erasure from the extension.  The fresh constant is
    replaced visibly by the caller-selected variable; certified descent below
    proves that this replacement branch is unreachable on original terms. -/
def eraseTerm {L : Language} (seedVar : Nat) :
    Term (FreshGroundLanguage L) → Term L
  | .var x => .var x
  | .const (Sum.inl c) => .const c
  | .const (Sum.inr _) => .var seedVar
  | .func f args => .func f (fun i => eraseTerm seedVar (args i))

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- An original-term certificate for a function application exposes a
    certificate for each immediate argument. -/
theorem IsOriginalTerm.func_arg {L : Language}
    {f : L.funSymbols}
    {args : Fin (L.funArity f) → Term (FreshGroundLanguage L)}
    (h : IsOriginalTerm (.func f args)) (i : Fin (L.funArity f)) :
    IsOriginalTerm (args i) := by
  cases h with
  | func _ _ hargs =>
      exact hargs i

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A fresh constant cannot carry an original-term certificate. -/
theorem freshConstant_not_original {L : Language} (u : Unit) :
    ¬ IsOriginalTerm
      (.const (Sum.inr u) : Term (FreshGroundLanguage L)) := by
  intro h
  cases h

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Certified descent of an original-symbol term back to the base language. -/
def lowerTerm {L : Language} :
    (t : Term (FreshGroundLanguage L)) → IsOriginalTerm t → Term L
  | .var x, _ => .var x
  | .const (Sum.inl c), _ => .const c
  | .const (Sum.inr u), h =>
      False.elim (freshConstant_not_original u h)
  | .func f args, h =>
      .func f (fun i => lowerTerm (args i) (h.func_arg i))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every lifted term is certified to use only original symbols. -/
theorem liftTerm_isOriginal {L : Language} (t : Term L) :
    IsOriginalTerm (liftTerm t) := by
  induction t with
  | var x =>
      exact .var x
  | const c =>
      exact .const c
  | func f args ih =>
      exact .func f (fun i => liftTerm (args i)) ih

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lifting after certified descent recovers the extension term exactly. -/
theorem liftTerm_lowerTerm {L : Language}
    {t : Term (FreshGroundLanguage L)} (h : IsOriginalTerm t) :
    liftTerm (lowerTerm t h) = t := by
  induction h with
  | var x =>
      rfl
  | const c =>
      rfl
  | func f args hargs ih =>
      simp only [lowerTerm, liftTerm]
      congr 1
      funext i
      exact ih i

-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- Certified descent is a left inverse of the term lift. -/
theorem lowerTerm_liftTerm {L : Language} (t : Term L) :
    lowerTerm (liftTerm t) (liftTerm_isOriginal t) = t := by
  induction t with
  | var x =>
      rfl
  | const c =>
      rfl
  | func f args ih =>
      simp only [lowerTerm, liftTerm]
      congr 1
      funext i
      exact ih i

-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- Total erasure is a left inverse of term lifting for every replacement
    variable. -/
theorem eraseTerm_liftTerm {L : Language}
    (seedVar : Nat) (t : Term L) :
    eraseTerm seedVar (liftTerm t) = t := by
  induction t with
  | var x =>
      rfl
  | const c =>
      rfl
  | func f args ih =>
      simp only [liftTerm, eraseTerm]
      congr 1
      funext i
      exact ih i

-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- The term embedding is injective. -/
theorem liftTerm_injective {L : Language} (hNoEq : L.withoutEquality) :
    Function.Injective (@liftTerm L) := by
  intro t
  induction t with
  | var x =>
      intro u h
      cases u with
      | var y =>
          exact congrArg Term.var (Term.var.inj h)
      | const => cases h
      | func => cases h
  | const c =>
      intro u h
      cases u with
      | var => cases h
      | const d =>
          exact congrArg Term.const
            (Sum.inl.inj (@Term.const.inj (FreshGroundLanguage L)
              (Sum.inl c) (Sum.inl d) h))
      | func => cases h
  | func f args ih =>
      intro u h
      cases u with
      | var => cases h
      | const => cases h
      | func g args' =>
          have hfg : f = g := (Term.func.inj h).1
          subst g
          congr 1
          funext i
          apply ih i
          have hargs :
              (fun i => liftTerm (args i)) =
                (fun i => liftTerm (args' i)) :=
            eq_of_heq (Term.func.inj h).2
          exact congrFun hargs i



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The fresh seed is not certified as an original-symbol term. -/
theorem seed_not_original {L : Language} :
    ¬ IsOriginalTerm (@seed L) :=
  freshConstant_not_original ()

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Structural predicate that every term of an atom uses original symbols. -/
def IsOriginalAtom {L : Language} (hNoEq : L.withoutEquality) :
    FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) → Prop
  | .predN _ args => ∀ i, IsOriginalTerm (args i)
  | .eq_ _ lhs rhs => IsOriginalTerm lhs ∧ IsOriginalTerm rhs

-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- Total structural erasure of an extension atom. -/
def eraseAtom {L : Language} (hNoEq : L.withoutEquality) (seedVar : Nat) :
    FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) → FOAtom L hNoEq
  | .predN P args =>
      .predN P (fun i => eraseTerm seedVar (args i))
  | .eq_ hL lhs rhs =>
      .eq_ hL (eraseTerm seedVar lhs) (eraseTerm seedVar rhs)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Certified descent of an original-symbol atom. -/
def lowerAtom {L : Language} (hNoEq : L.withoutEquality)
    (atom : FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (h : IsOriginalAtom (hNoEq := by first | exact hNoEq | done) atom) : FOAtom L hNoEq :=
  match atom with
  | .predN P args =>
      .predN P (fun i => lowerTerm (args i) (h i))
  | .eq_ hL lhs rhs =>
      .eq_ hL (lowerTerm lhs h.1) (lowerTerm rhs h.2)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every lifted atom is certified to use only original symbols. -/
theorem liftAtom_isOriginal {L : Language} (hNoEq : L.withoutEquality) (atom : FOAtom L hNoEq) :
    IsOriginalAtom (hNoEq := by first | exact hNoEq | done) (liftAtom (hNoEq := by first | exact hNoEq | done) atom) := by
  cases atom with
  | predN P args =>
      exact fun i => liftTerm_isOriginal (args i)
  | eq_ hL lhs rhs =>
      exact ⟨liftTerm_isOriginal lhs, liftTerm_isOriginal rhs⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lifting after certified atom descent recovers the atom exactly. -/
theorem liftAtom_lowerAtom {L : Language} (hNoEq : L.withoutEquality)
    (atom : FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (h : IsOriginalAtom (hNoEq := by first | exact hNoEq | done) atom) :
    liftAtom (hNoEq := by first | exact hNoEq | done) (lowerAtom (hNoEq := by first | exact hNoEq | done) atom h) = atom := by
  cases atom with
  | predN P args =>
      simp only [lowerAtom, liftAtom]
      congr 1
      funext i
      exact liftTerm_lowerTerm (h i)
  | eq_ hL lhs rhs =>
      simp only [lowerAtom, liftAtom]
      congr 1
      · exact liftTerm_lowerTerm h.1
      · exact liftTerm_lowerTerm h.2



-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- The atom embedding is injective. -/
theorem liftAtom_injective {L : Language} (hNoEq : L.withoutEquality) :
    Function.Injective (@liftAtom (hNoEq := by first | exact hNoEq | done) L) := by
  intro atom₁ atom₂ h
  cases atom₁ <;> cases atom₂
  · have h' := FOAtomCore.predN.inj h
    cases h'.1
    congr 1
    funext i
    apply liftTerm_injective (hNoEq := by first | exact hNoEq | done)
    exact congrFun (eq_of_heq h'.2) i
  · cases h
  · cases h
  · have h' := FOAtomCore.eq_.inj h
    rw [liftTerm_injective (hNoEq := by first | exact hNoEq | done) h'.1, liftTerm_injective (hNoEq := by first | exact hNoEq | done) h'.2]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Structural predicate that a literal's atom uses original symbols. -/
def IsOriginalLiteral {L : Language} (hNoEq : L.withoutEquality) :
    FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) → Prop
  | .pos atom | .neg atom => IsOriginalAtom (hNoEq := by first | exact hNoEq | done) atom

-- retained: used by LCS.FOResolution.Method.GroundExtension, LCS.Resolution.Method.Erase, LCS.Resolution.Method.Erase.Proofs, LCS.Resolution.Method.ReverseExamples, LCS.Resolution.Method.ReverseExamples.Proofs, LCS.Resolution.Method.ReverseGrowth.Proofs, LCS.Resolution.Method.ReverseTree
/-- Total structural erasure of an extension literal. -/
def eraseLiteral {L : Language} (hNoEq : L.withoutEquality) (seedVar : Nat) :
    FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) → FOLiteral L hNoEq
  | .pos atom => .pos (eraseAtom (hNoEq := by first | exact hNoEq | done) seedVar atom)
  | .neg atom => .neg (eraseAtom (hNoEq := by first | exact hNoEq | done) seedVar atom)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Certified descent of an original-symbol literal. -/
def lowerLiteral {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (h : IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit) : FOLiteral L hNoEq :=
  match lit with
  | .pos atom => .pos (lowerAtom (hNoEq := by first | exact hNoEq | done) atom h)
  | .neg atom => .neg (lowerAtom (hNoEq := by first | exact hNoEq | done) atom h)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every lifted literal is certified to use only original symbols. -/
theorem liftLiteral_isOriginal {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) (liftLiteral (hNoEq := by first | exact hNoEq | done) lit) := by
  cases lit <;> apply liftAtom_isOriginal (hNoEq := by first | exact hNoEq | done)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lifting after certified literal descent recovers the literal exactly. -/
theorem liftLiteral_lowerLiteral {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (h : IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit) :
    liftLiteral (hNoEq := by first | exact hNoEq | done) (lowerLiteral (hNoEq := by first | exact hNoEq | done) lit h) = lit := by
  cases lit with
  | pos atom =>
      exact congrArg FOLiteralCore.pos (liftAtom_lowerAtom (hNoEq := by first | exact hNoEq | done) atom h)
  | neg atom =>
      exact congrArg FOLiteralCore.neg (liftAtom_lowerAtom (hNoEq := by first | exact hNoEq | done) atom h)



-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- The literal embedding is injective. -/
theorem liftLiteral_injective {L : Language} (hNoEq : L.withoutEquality) :
    Function.Injective (@liftLiteral (hNoEq := by first | exact hNoEq | done) L) := by
  intro lit₁ lit₂ h
  cases lit₁ <;> cases lit₂
  · exact congrArg FOLiteralCore.pos
      (liftAtom_injective (hNoEq := by first | exact hNoEq | done) (FOLiteralCore.pos.inj h))
  · cases h
  · cases h
  · exact congrArg FOLiteralCore.neg
      (liftAtom_injective (hNoEq := by first | exact hNoEq | done) (FOLiteralCore.neg.inj h))

-- ATTACH-BLOCKER: unsupported untagged inductive
/-- Structural certificate that every literal of a clause uses only original
    symbols.  This list-indexed form supports total constructive descent. -/
inductive IsOriginalClause {L : Language} (hNoEq : L.withoutEquality) :
    FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) → Prop where
  | nil : IsOriginalClause (hNoEq := by first | exact hNoEq | done) []
  | cons {lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
      {rest : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
      (hlit : IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit)
      (hrest : IsOriginalClause (hNoEq := by first | exact hNoEq | done) rest) :
      IsOriginalClause (hNoEq := by first | exact hNoEq | done) (lit :: rest)

-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- Total pointwise erasure of an extension clause. -/
def eraseClause {L : Language} (hNoEq : L.withoutEquality) (seedVar : Nat)
    (C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) : FOClause L hNoEq :=
  C.map (eraseLiteral (hNoEq := by first | exact hNoEq | done) seedVar)

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- An original-clause certificate exposes its head-literal certificate. -/
theorem IsOriginalClause.head {L : Language} (hNoEq : L.withoutEquality)
    {lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    {rest : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (h : IsOriginalClause (hNoEq := by first | exact hNoEq | done) (lit :: rest)) :
    IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit := by
  cases h with
  | cons hlit _ =>
      exact hlit

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- An original-clause certificate exposes its tail certificate. -/
theorem IsOriginalClause.tail {L : Language} (hNoEq : L.withoutEquality)
    {lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    {rest : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (h : IsOriginalClause (hNoEq := by first | exact hNoEq | done) (lit :: rest)) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) rest := by
  cases h with
  | cons _ hrest =>
      exact hrest

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Certified descent of an original-symbol clause. -/
def lowerClause {L : Language} (hNoEq : L.withoutEquality) :
    (C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) → IsOriginalClause (hNoEq := by first | exact hNoEq | done) C → FOClause L hNoEq
  | [], _ => []
  | lit :: rest, h =>
      lowerLiteral (hNoEq := by first | exact hNoEq | done) lit h.head :: lowerClause (hNoEq := by first | exact hNoEq | done) rest h.tail

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every lifted clause is certified to use only original symbols. -/
theorem liftClause_isOriginal {L : Language} (hNoEq : L.withoutEquality) (C : FOClause L hNoEq) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) C) := by
  induction C with
  | nil =>
      exact .nil
  | cons lit rest ih =>
      exact .cons (liftLiteral_isOriginal (hNoEq := by first | exact hNoEq | done) lit) ih

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lifting after certified clause descent recovers the clause exactly. -/
theorem liftClause_lowerClause {L : Language} (hNoEq : L.withoutEquality)
    {C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (h : IsOriginalClause (hNoEq := by first | exact hNoEq | done) C) :
    liftClause (hNoEq := by first | exact hNoEq | done) (lowerClause (hNoEq := by first | exact hNoEq | done) C h) = C := by
  induction h with
  | nil =>
      rfl
  | cons hlit hrest ih =>
      change
        liftLiteral (hNoEq := by first | exact hNoEq | done) (lowerLiteral (hNoEq := by first | exact hNoEq | done) _ hlit) ::
            liftClause (hNoEq := by first | exact hNoEq | done) (lowerClause (hNoEq := by first | exact hNoEq | done) _ hrest) =
          _ :: _
      rw [liftLiteral_lowerLiteral (hNoEq := by first | exact hNoEq | done) _ hlit, ih]



-- retained: used by LCS.FOResolution.Method.Completeness.Completeness, LCS.FOResolution.Method.GroundExtension
/-- Pointwise clause lifting is injective. -/
theorem liftClause_injective {L : Language} (hNoEq : L.withoutEquality) :
    Function.Injective (@liftClause (hNoEq := by first | exact hNoEq | done) L) := by
  intro C
  induction C with
  | nil =>
      intro D h
      cases D with
      | nil => rfl
      | cons => cases h
  | cons lit rest ih =>
      intro D h
      cases D with
      | nil => cases h
      | cons lit' rest' =>
          have h' := List.cons.inj h
          rw [liftLiteral_injective (hNoEq := by first | exact hNoEq | done) h'.1, ih h'.2]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Structural image predicate for substitutions. -/
def IsOriginalSubst {L : Language}
    (sigma : Nat → Term (FreshGroundLanguage L)) : Prop :=
  ∀ x, IsOriginalTerm (sigma x)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Certified pointwise descent of an original-symbol substitution. -/
def lowerSubst {L : Language}
    (sigma : Nat → Term (FreshGroundLanguage L))
    (h : IsOriginalSubst sigma) : Nat → Term L :=
  fun x => lowerTerm (sigma x) (h x)



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lifting after certified substitution descent is exact. -/
theorem liftSubst_lowerSubst {L : Language}
    (sigma : Nat → Term (FreshGroundLanguage L))
    (h : IsOriginalSubst sigma) :
    liftSubst (lowerSubst sigma h) = sigma := by
  funext x
  exact liftTerm_lowerTerm (h x)



-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Term lifting commutes with simultaneous substitution. -/
theorem liftTerm_termSubstAll {L : Language}
    (t : Term L) (sigma : Nat → Term L) :
    liftTerm (termSubstAll t sigma) =
      termSubstAll (liftTerm t) (liftSubst sigma) := by
  induction t with
  | var x =>
      rfl
  | const c =>
      rfl
  | func f args ih =>
      simp only [termSubstAll, liftTerm]
      congr 1
      funext i
      exact ih i

-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- Erasing after substituting into a lifted term equals base-language
    substitution by the pointwise-erased extension substitution. -/
theorem eraseTerm_termSubstAll_liftTerm {L : Language}
    (seedVar : Nat) (t : Term L)
    (sigma : Nat → Term (FreshGroundLanguage L)) :
    eraseTerm seedVar
        (termSubstAll (liftTerm t) sigma) =
      termSubstAll t (fun x => eraseTerm seedVar (sigma x)) := by
  induction t with
  | var x =>
      rfl
  | const c =>
      rfl
  | func f args ih =>
      simp only [liftTerm, termSubstAll, eraseTerm]
      congr 1
      funext i
      exact ih i

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- If substituting a term produces only original symbols, then the source
    term itself used only original symbols.  Substitution cannot erase a
    fresh constant already present in the source. -/
theorem IsOriginalTerm.of_subst {L : Language}
    (t : Term (FreshGroundLanguage L))
    (sigma : Nat → Term (FreshGroundLanguage L))
    (h : IsOriginalTerm (termSubstAll t sigma)) :
    IsOriginalTerm t := by
  induction t with
  | var x =>
      exact .var x
  | const c =>
      cases c with
      | inl c =>
          exact .const c
      | inr u =>
          cases u
          exact (seed_not_original h).elim
  | func f args ih =>
      cases h with
      | func _ _ hargs =>
          exact @IsOriginalTerm.func L f args
            (fun i => ih i (hargs i))

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Atom lifting commutes with simultaneous substitution. -/
theorem liftAtom_subst {L : Language} (hNoEq : L.withoutEquality)
    (atom : FOAtom L hNoEq) (sigma : Nat → Term L) :
    liftAtom (hNoEq := by first | exact hNoEq | done) (atom.subst (hNoEq := by first | exact hNoEq | done) sigma) =
      (liftAtom (hNoEq := by first | exact hNoEq | done) atom).subst (hNoEq := by first | exact hNoEq | done) (liftSubst sigma) := by
  cases atom with
  | predN P args =>
      simp only [FOAtomCore.subst, FOAtomCore.mapTerms, liftAtom]
      congr 1
      funext i
      exact liftTerm_termSubstAll (args i) sigma
  | eq_ hL lhs rhs =>
      simp only [FOAtomCore.subst, FOAtomCore.mapTerms, liftAtom]
      rw [liftTerm_termSubstAll lhs sigma,
        liftTerm_termSubstAll rhs sigma]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Literal lifting commutes with simultaneous substitution. -/
theorem liftLiteral_substLit {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) (sigma : Nat → Term L) :
    liftLiteral (hNoEq := by first | exact hNoEq | done) (substLit (hNoEq := by first | exact hNoEq | done) sigma lit) =
      substLit (hNoEq := by first | exact hNoEq | done) (liftSubst sigma) (liftLiteral (hNoEq := by first | exact hNoEq | done) lit) := by
  cases lit <;> simp only [substLit, liftLiteral] <;>
    rw [liftAtom_subst (hNoEq := by first | exact hNoEq | done)]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Clause lifting commutes with simultaneous substitution. -/
theorem liftClause_substLits {L : Language} (hNoEq : L.withoutEquality)
    (C : FOClause L hNoEq) (sigma : Nat → Term L) :
    liftClause (hNoEq := by first | exact hNoEq | done) (substLits (hNoEq := by first | exact hNoEq | done) sigma C) =
      substLits (hNoEq := by first | exact hNoEq | done) (liftSubst sigma) (liftClause (hNoEq := by first | exact hNoEq | done) C) := by
  simp only [substLits, liftClause, List.map_map]
  apply List.map_congr_left
  intro lit _
  exact liftLiteral_substLit (hNoEq := by first | exact hNoEq | done) lit sigma

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Original-symbol terms stay original under original-symbol substitutions. -/
theorem IsOriginalTerm.subst {L : Language} (hNoEq : L.withoutEquality)
    {t : Term (FreshGroundLanguage L)}
    (ht : IsOriginalTerm t)
    (sigma : Nat → Term (FreshGroundLanguage L))
    (hsigma : IsOriginalSubst sigma) :
    IsOriginalTerm (termSubstAll t sigma) := by
  rw [← liftTerm_lowerTerm ht, ← liftSubst_lowerSubst sigma hsigma,
    ← liftTerm_termSubstAll]
  exact liftTerm_isOriginal _

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Original-symbol atoms stay original under original-symbol substitutions. -/
theorem IsOriginalAtom.subst {L : Language} (hNoEq : L.withoutEquality)
    {atom : FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hatom : IsOriginalAtom (hNoEq := by first | exact hNoEq | done) atom)
    (sigma : Nat → Term (FreshGroundLanguage L))
    (hsigma : IsOriginalSubst sigma) :
    IsOriginalAtom (hNoEq := by first | exact hNoEq | done) (atom.subst (hNoEq := by first | exact hNoEq | done) sigma) := by
  rw [← liftAtom_lowerAtom (hNoEq := by first | exact hNoEq | done) atom hatom,
    ← liftSubst_lowerSubst sigma hsigma,
    ← liftAtom_subst (hNoEq := by first | exact hNoEq | done)]
  exact liftAtom_isOriginal (hNoEq := by first | exact hNoEq | done) _

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Original-symbol literals stay original under original-symbol substitutions. -/
theorem IsOriginalLiteral.subst {L : Language} (hNoEq : L.withoutEquality)
    {lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hlit : IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit)
    (sigma : Nat → Term (FreshGroundLanguage L))
    (hsigma : IsOriginalSubst sigma) :
    IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) (substLit (hNoEq := by first | exact hNoEq | done) sigma lit) := by
  rw [← liftLiteral_lowerLiteral (hNoEq := by first | exact hNoEq | done) lit hlit,
    ← liftSubst_lowerSubst sigma hsigma,
    ← liftLiteral_substLit (hNoEq := by first | exact hNoEq | done)]
  exact liftLiteral_isOriginal (hNoEq := by first | exact hNoEq | done) _

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Original-symbol clauses stay original under original-symbol substitutions. -/
theorem IsOriginalClause.subst {L : Language} (hNoEq : L.withoutEquality)
    {C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hC : IsOriginalClause (hNoEq := by first | exact hNoEq | done) C)
    (sigma : Nat → Term (FreshGroundLanguage L))
    (hsigma : IsOriginalSubst sigma) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) (substLits (hNoEq := by first | exact hNoEq | done) sigma C) := by
  rw [← liftClause_lowerClause (hNoEq := by first | exact hNoEq | done) hC,
    ← liftSubst_lowerSubst sigma hsigma,
    ← liftClause_substLits (hNoEq := by first | exact hNoEq | done)]
  exact liftClause_isOriginal (hNoEq := by first | exact hNoEq | done) _

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Originality descends to every member literal of a certified clause. -/
theorem IsOriginalClause.literal_of_mem {L : Language} (hNoEq : L.withoutEquality)
    {C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hC : IsOriginalClause (hNoEq := by first | exact hNoEq | done) C)
    {lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hMem : lit ∈ C) :
    IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit := by
  induction hC with
  | nil =>
      exact (List.not_mem_nil hMem).elim
  | cons hlit hrest ih =>
      rcases List.mem_cons.mp hMem with rfl | hMem
      · exact hlit
      · exact ih hMem

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Any list-subset of an original clause is itself original. -/
theorem IsOriginalClause.of_sublist {L : Language} (hNoEq : L.withoutEquality)
    {sub full : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hFull : IsOriginalClause (hNoEq := by first | exact hNoEq | done) full)
    (hSub : IsSublist sub full) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) sub := by
  induction sub with
  | nil =>
      exact .nil
  | cons lit rest ih =>
      exact .cons
        (hFull.literal_of_mem (hNoEq := by first | exact hNoEq | done) (hSub lit List.mem_cons_self))
        (ih (fun item hMem =>
          hSub item (List.mem_cons_of_mem lit hMem)))

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Appending two original clauses preserves originality. -/
theorem IsOriginalClause.append {L : Language} (hNoEq : L.withoutEquality)
    {left right : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hLeft : IsOriginalClause (hNoEq := by first | exact hNoEq | done) left)
    (hRight : IsOriginalClause (hNoEq := by first | exact hNoEq | done) right) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) (left ++ right) := by
  induction hLeft with
  | nil =>
      exact hRight
  | cons hlit _ ih =>
      exact .cons hlit ih

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Conjugating an original literal preserves its symbol provenance. -/
theorem IsOriginalLiteral.conjugate {L : Language} (hNoEq : L.withoutEquality)
    {lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hLit : IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit) :
    IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit.conjugate := by
  cases lit <;> exact hLit

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Conjugating an original literal list preserves originality. -/
theorem IsOriginalClause.conjugate {L : Language} (hNoEq : L.withoutEquality)
    {lits : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hLits : IsOriginalClause (hNoEq := by first | exact hNoEq | done) lits) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) (LitSetConjugate (hNoEq := by first | exact hNoEq | done) lits) := by
  induction hLits with
  | nil =>
      exact .nil
  | cons hlit _ ih =>
      exact .cons hlit.conjugate ih

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Taking the total same-sign absolute-value operation preserves an
    original-symbol certificate. -/
theorem IsOriginalClause.abs {L : Language} (hNoEq : L.withoutEquality)
    {lits : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hLits : IsOriginalClause (hNoEq := by first | exact hNoEq | done) lits) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) (LitSetAbs (hNoEq := by first | exact hNoEq | done) lits) := by
  cases lits with
  | nil =>
      exact .nil
  | cons lit rest =>
      cases lit with
      | pos =>
          exact hLits
      | neg =>
          exact hLits.conjugate

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Removing literals from an original clause preserves originality. -/
theorem IsOriginalClause.listDiff {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    {C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hC : IsOriginalClause (hNoEq := by first | exact hNoEq | done) C)
    (removed : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) (Method.listDiff C removed) :=
  hC.of_sublist (hNoEq := by first | exact hNoEq | done) (fun _ hMem => (List.mem_filter.mp hMem).1)

-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- Literal lifting preserves conjugation. -/
theorem liftLiteral_conjugate {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    liftLiteral (hNoEq := by first | exact hNoEq | done) lit.conjugate = (liftLiteral (hNoEq := by first | exact hNoEq | done) lit).conjugate := by
  cases lit <;> rfl

-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- Clause lifting distributes over append. -/
theorem liftClause_append {L : Language} (hNoEq : L.withoutEquality)
    (left right : FOClause L hNoEq) :
    liftClause (hNoEq := by first | exact hNoEq | done) (left ++ right) = liftClause (hNoEq := by first | exact hNoEq | done) left ++ liftClause (hNoEq := by first | exact hNoEq | done) right :=
  List.map_append

end FreshGroundLanguage
end LCS.FOResolution.Method
end

