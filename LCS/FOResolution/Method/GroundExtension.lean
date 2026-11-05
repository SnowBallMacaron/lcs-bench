import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.ResolutionTrees
import Attach
import LCS.FOResolution.Method.GroundExtension.ProofsStamp

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
namespace FreshGroundLanguage

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Clause lifting commutes with literal-set conjugation. -/
theorem liftClause_conjugate {L : Language} (hNoEq : L.withoutEquality) (lits : FOClause L hNoEq) :
    liftClause (hNoEq := by first | exact hNoEq | done) (LitSetConjugate (hNoEq := by first | exact hNoEq | done) lits) =
      LitSetConjugate (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) lits) := by
  induction lits with
  | nil =>
      rfl
  | cons lit rest ih =>
      change
        liftLiteral (hNoEq := by first | exact hNoEq | done) lit.conjugate :: liftClause (hNoEq := by first | exact hNoEq | done) (LitSetConjugate (hNoEq := by first | exact hNoEq | done) rest) =
          (liftLiteral (hNoEq := by first | exact hNoEq | done) lit).conjugate ::
            LitSetConjugate (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) rest)
      rw [liftLiteral_conjugate (hNoEq := by first | exact hNoEq | done), ih]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Clause lifting commutes with the total literal-set absolute value. -/
theorem liftClause_abs {L : Language} (hNoEq : L.withoutEquality) (lits : FOClause L hNoEq) :
    liftClause (hNoEq := by first | exact hNoEq | done) (LitSetAbs (hNoEq := by first | exact hNoEq | done) lits) = LitSetAbs (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) lits) := by
  cases lits with
  | nil =>
      rfl
  | cons lit rest =>
      cases lit with
      | pos =>
          rfl
      | neg =>
          exact liftClause_conjugate (hNoEq := by first | exact hNoEq | done) _

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Membership in a lifted clause reflects through the injective literal
    embedding. -/
theorem liftLiteral_mem_liftClause_iff {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral L hNoEq) (C : FOClause L hNoEq) :
    liftLiteral (hNoEq := by first | exact hNoEq | done) lit ∈ liftClause (hNoEq := by first | exact hNoEq | done) C ↔ lit ∈ C := by
  constructor
  · intro hMem
    obtain ⟨source, hSource, hEq⟩ := List.mem_map.mp hMem
    exact liftLiteral_injective (hNoEq := by first | exact hNoEq | done) hEq ▸ hSource
  · exact fun hMem => List.mem_map.mpr ⟨lit, hMem, rfl⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lifting commutes with list difference because the literal embedding is
    injective. -/
theorem liftClause_listDiff {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    (A B : FOClause L hNoEq) :
    liftClause (hNoEq := by first | exact hNoEq | done) (Method.listDiff A B) =
      Method.listDiff (liftClause (hNoEq := by first | exact hNoEq | done) A) (liftClause (hNoEq := by first | exact hNoEq | done) B) := by
  have hContains (a : FOLiteral L hNoEq) :
      (liftClause (hNoEq := by first | exact hNoEq | done) B).contains (liftLiteral (hNoEq := by first | exact hNoEq | done) a) = B.contains a := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro ha
      obtain ⟨b, hb, hba⟩ :=
        List.mem_map.mp (List.contains_iff_mem.mp ha)
      have : b = a := liftLiteral_injective (hNoEq := by first | exact hNoEq | done) hba
      subst b
      exact List.contains_iff_mem.mpr hb
    · intro ha
      exact List.contains_iff_mem.mpr
        (List.mem_map_of_mem (f := liftLiteral (hNoEq := by first | exact hNoEq | done))
          (List.contains_iff_mem.mp ha))
  unfold Method.listDiff liftClause
  rw [List.filter_map]
  apply congrArg (List.map (liftLiteral (hNoEq := by first | exact hNoEq | done)))
  apply List.filter_congr
  intro a _
  simp only [Function.comp_apply]
  congr 1
  exact (hContains a).symm

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Term-variable collection is unchanged by lifting. -/
theorem termVars_liftTerm {L : Language} (t : Term L) :
    termVars (liftTerm t) = termVars t := by
  induction t with
  | var =>
      rfl
  | const =>
      rfl
  | func f args ih =>
      ext x
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (congrFun (ih i) x).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (congrFun (ih i) x).mpr hi⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Atom-variable collection is unchanged by lifting. -/
theorem atomVars_liftAtom {L : Language} (hNoEq : L.withoutEquality) (atom : FOAtom L hNoEq) :
    (liftAtom (hNoEq := by first | exact hNoEq | done) atom).vars = atom.vars := by
  cases atom with
  | predN P args =>
      ext x
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (congrFun (termVars_liftTerm (args i)) x).mp hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, (congrFun (termVars_liftTerm (args i)) x).mpr hi⟩
  | eq_ hEq lhs rhs =>
      ext x
      simp only [liftAtom, FOAtomCore.vars]
      rw [congrFun (termVars_liftTerm lhs) x,
        congrFun (termVars_liftTerm rhs) x]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Literal-variable collection is unchanged by lifting. -/
theorem literalVars_liftLiteral {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    (liftLiteral (hNoEq := by first | exact hNoEq | done) lit).vars = lit.vars := by
  cases lit <;> exact atomVars_liftAtom (hNoEq := by first | exact hNoEq | done) _

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Clause free-variable collection is unchanged by lifting. -/
theorem clauseFV_liftClause {L : Language} (hNoEq : L.withoutEquality) (C : FOClause L hNoEq) :
    clauseFV (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) C) = clauseFV (hNoEq := by first | exact hNoEq | done) C := by
  ext x
  constructor
  · rintro ⟨lit, hMem, hx⟩
    obtain ⟨source, hSource, rfl⟩ := List.mem_map.mp hMem
    exact ⟨source, hSource,
      (congrFun (literalVars_liftLiteral (hNoEq := by first | exact hNoEq | done) source) x).mp hx⟩
  · rintro ⟨lit, hMem, hx⟩
    exact ⟨liftLiteral (hNoEq := by first | exact hNoEq | done) lit, List.mem_map.mpr ⟨lit, hMem, rfl⟩,
      (congrFun (literalVars_liftLiteral (hNoEq := by first | exact hNoEq | done) lit) x).mpr hx⟩













-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A list-subset relation between lifted clauses reflects to the base
    clauses. -/
theorem isSublist_of_liftClause {L : Language} (hNoEq : L.withoutEquality)
    {sub full : FOClause L hNoEq}
    (hSub : IsSublist (liftClause (hNoEq := by first | exact hNoEq | done) sub) (liftClause (hNoEq := by first | exact hNoEq | done) full)) :
    IsSublist sub full := by
  intro lit hMem
  apply (liftLiteral_mem_liftClause_iff (hNoEq := by first | exact hNoEq | done) lit full).mp
  exact hSub (liftLiteral (hNoEq := by first | exact hNoEq | done) lit)
    ((liftLiteral_mem_liftClause_iff (hNoEq := by first | exact hNoEq | done) lit sub).mpr hMem)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Positivity of a lifted literal list reflects to the base list. -/
theorem litSetPositive_of_liftClause {L : Language} (hNoEq : L.withoutEquality)
    {lits : FOClause L hNoEq}
    (hPositive : LitSetPositive (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) lits)) :
    LitSetPositive (hNoEq := by first | exact hNoEq | done) lits := by
  intro lit hMem
  obtain ⟨atom, hEq⟩ := hPositive (liftLiteral (hNoEq := by first | exact hNoEq | done) lit)
    ((liftLiteral_mem_liftClause_iff (hNoEq := by first | exact hNoEq | done) lit lits).mpr hMem)
  cases lit with
  | pos source =>
      exact ⟨source, rfl⟩
  | neg =>
      cases hEq

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Negativity of a lifted literal list reflects to the base list. -/
theorem litSetNegative_of_liftClause {L : Language} (hNoEq : L.withoutEquality)
    {lits : FOClause L hNoEq}
    (hNegative : LitSetNegative (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) lits)) :
    LitSetNegative (hNoEq := by first | exact hNoEq | done) lits := by
  intro lit hMem
  obtain ⟨atom, hEq⟩ := hNegative (liftLiteral (hNoEq := by first | exact hNoEq | done) lit)
    ((liftLiteral_mem_liftClause_iff (hNoEq := by first | exact hNoEq | done) lit lits).mpr hMem)
  cases lit with
  | pos =>
      cases hEq
  | neg source =>
      exact ⟨source, rfl⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Same-sign and opposite-sign conditions reflect through clause lifting. -/
theorem litSetSameSign_of_liftClause {L : Language} (hNoEq : L.withoutEquality)
    {lits : FOClause L hNoEq}
    (hSame : LitSetSameSign (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) lits)) :
    LitSetSameSign (hNoEq := by first | exact hNoEq | done) lits := by
  rcases hSame with hPositive | hNegative
  · exact Or.inl (litSetPositive_of_liftClause (hNoEq := by first | exact hNoEq | done) hPositive)
  · exact Or.inr (litSetNegative_of_liftClause (hNoEq := by first | exact hNoEq | done) hNegative)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
theorem litSetOppositeSign_of_liftClause {L : Language} (hNoEq : L.withoutEquality)
    {left right : FOClause L hNoEq}
    (hOpposite :
      LitSetOppositeSign (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) left) (liftClause (hNoEq := by first | exact hNoEq | done) right)) :
    LitSetOppositeSign (hNoEq := by first | exact hNoEq | done) left right := by
  rcases hOpposite with ⟨hLeft, hRight⟩ | ⟨hLeft, hRight⟩
  · exact Or.inl ⟨litSetPositive_of_liftClause (hNoEq := by first | exact hNoEq | done) hLeft,
      litSetNegative_of_liftClause (hNoEq := by first | exact hNoEq | done) hRight⟩
  · exact Or.inr ⟨litSetNegative_of_liftClause (hNoEq := by first | exact hNoEq | done) hLeft,
      litSetPositive_of_liftClause (hNoEq := by first | exact hNoEq | done) hRight⟩

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The common predicate condition reflects through clause lifting. -/
theorem litSetSamePred_of_liftClause {L : Language} (hNoEq : L.withoutEquality)
    {lits : FOClause L hNoEq}
    (hPred : LitSetSamePred (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) lits)) :
    LitSetSamePred (hNoEq := by first | exact hNoEq | done) lits := by
  obtain ⟨P, hP⟩ := hPred
  refine ⟨P, ?_⟩
  intro lit hMem
  obtain ⟨liftedArgs, hEq⟩ := hP (liftLiteral (hNoEq := by first | exact hNoEq | done) lit)
    ((liftLiteral_mem_liftClause_iff (hNoEq := by first | exact hNoEq | done) lit lits).mpr hMem)
  cases lit with
  | pos atom | neg atom =>
      cases atom with
      | predN Q args =>
          simp only [liftLiteral, liftAtom, FOLiteral.formula,
            FOAtomCore.toFormula] at hEq
          have hQP : Q = P := (FormulaN.predN.inj hEq).1
          subst P
          exact ⟨args, rfl⟩
      | eq_ =>
          cases hEq

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- A separating-pair certificate for lifted data reflects to the base
    language. -/
theorem isSeparatingPair_of_lift {L : Language} (hNoEq : L.withoutEquality)
    {rho rho' : Nat → Term L}
    {A B : FOClause L hNoEq}
    (hSeparating :
      IsSeparatingPair (hNoEq := by first | exact hNoEq | done) (liftSubst rho) (liftSubst rho')
        (liftClause (hNoEq := by first | exact hNoEq | done) A) (liftClause (hNoEq := by first | exact hNoEq | done) B)) :
    IsSeparatingPair (hNoEq := by first | exact hNoEq | done) rho rho' A B := by
  obtain ⟨hVar, hVar', hInjective, hInjective', hDisjoint,
    hOutside, hOutside'⟩ := hSeparating
  have hRange :
      substRangeOnSet (liftSubst rho) (clauseFV (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) A)) =
        substRangeOnSet rho (clauseFV (hNoEq := by first | exact hNoEq | done) A) := by
    ext n
    constructor
    · rintro ⟨x, hx, hEq⟩
      refine ⟨x, ?_, liftTerm_injective (hNoEq := by first | exact hNoEq | done) hEq⟩
      rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)] at hx
    · rintro ⟨x, hx, hEq⟩
      refine ⟨x, ?_, ?_⟩
      · rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)]
      · exact congrArg liftTerm hEq
  have hRange' :
      substRangeOnSet (liftSubst rho') (clauseFV (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) B)) =
        substRangeOnSet rho' (clauseFV (hNoEq := by first | exact hNoEq | done) B) := by
    ext n
    constructor
    · rintro ⟨x, hx, hEq⟩
      refine ⟨x, ?_, liftTerm_injective (hNoEq := by first | exact hNoEq | done) hEq⟩
      rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)] at hx
    · rintro ⟨x, hx, hEq⟩
      refine ⟨x, ?_, ?_⟩
      · rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)]
      · exact congrArg liftTerm hEq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hEq⟩ := hVar x (by
      rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)])
    exact ⟨y, liftTerm_injective (hNoEq := by first | exact hNoEq | done) hEq⟩
  · intro x hx
    obtain ⟨y, hEq⟩ := hVar' x (by
      rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)])
    exact ⟨y, liftTerm_injective (hNoEq := by first | exact hNoEq | done) hEq⟩
  · intro x y hx hy hEq
    apply hInjective x y
    · rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)]
    · rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)]
    · exact congrArg liftTerm hEq
  · intro x y hx hy hEq
    apply hInjective' x y
    · rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)]
    · rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)]
    · exact congrArg liftTerm hEq
  · rwa [hRange, hRange'] at hDisjoint
  · intro x hx
    apply liftTerm_injective (hNoEq := by first | exact hNoEq | done)
    apply hOutside x
    rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)]
  · intro x hx
    apply liftTerm_injective (hNoEq := by first | exact hNoEq | done)
    apply hOutside' x
    rwa [clauseFV_liftClause (hNoEq := by first | exact hNoEq | done)]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Structural certificate that every term on both sides of an equation
    system uses only original symbols. -/
def IsOriginalPairSystem {L : Language}
    (pairs : List
      (Term (FreshGroundLanguage L) × Term (FreshGroundLanguage L))) : Prop :=
  ∀ p, p ∈ pairs → IsOriginalTerm p.1 ∧ IsOriginalTerm p.2

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pointwise total erasure of an extension-language substitution. -/
def eraseSubst {L : Language} (seedVar : Nat)
    (sigma : Nat → Term (FreshGroundLanguage L)) : Nat → Term L :=
  fun x => eraseTerm seedVar (sigma x)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- On an original term, total erasure agrees with certified descent,
    independently of the replacement variable. -/
theorem eraseTerm_eq_lowerTerm {L : Language}
    (seedVar : Nat)
    {t : Term (FreshGroundLanguage L)}
    (h : IsOriginalTerm t) :
    eraseTerm seedVar t = lowerTerm t h := by
  induction h with
  | var =>
      rfl
  | const =>
      rfl
  | func f args hargs ih =>
      simp only [eraseTerm, lowerTerm]
      congr 1
      funext i
      exact ih i

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pointwise erasure of an original substitution agrees with certified
    substitution descent. -/
theorem eraseSubst_eq_lowerSubst {L : Language}
    (seedVar : Nat)
    (sigma : Nat → Term (FreshGroundLanguage L))
    (h : IsOriginalSubst sigma) :
    eraseSubst seedVar sigma = lowerSubst sigma h := by
  funext x
  exact eraseTerm_eq_lowerTerm seedVar (h x)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Lifting does not change a term's free-variable set. -/
theorem termFV_liftTerm {L : Language} (t : Term L) :
    termFV (liftTerm t) = termFV t := by
  induction t with
  | var =>
      rfl
  | const =>
      rfl
  | func f args ih =>
      simp only [liftTerm, termFV]
      congr 1
      funext i
      exact ih i

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Erasing an original term does not change its free-variable set. -/
theorem termFV_eraseTerm_of_original {L : Language}
    (seedVar : Nat)
    {t : Term (FreshGroundLanguage L)}
    (h : IsOriginalTerm t) :
    termFV (eraseTerm seedVar t) = termFV t := by
  rw [eraseTerm_eq_lowerTerm seedVar h,
    ← termFV_liftTerm (lowerTerm t h),
    liftTerm_lowerTerm h]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Erasure commutes with substitution when the source term is original. -/
theorem eraseTerm_termSubstAll_of_original {L : Language}
    (seedVar : Nat)
    {t : Term (FreshGroundLanguage L)}
    (h : IsOriginalTerm t)
    (sigma : Nat → Term (FreshGroundLanguage L)) :
    eraseTerm seedVar (termSubstAll t sigma) =
      termSubstAll (eraseTerm seedVar t) (eraseSubst seedVar sigma) := by
  rw [← liftTerm_lowerTerm h,
    eraseTerm_termSubstAll_liftTerm,
    eraseTerm_liftTerm]
  rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pointwise erasure of both endpoints of an equation. -/
def eraseTermPair {L : Language} (seedVar : Nat)
    (p : Term (FreshGroundLanguage L) ×
      Term (FreshGroundLanguage L)) : Term L × Term L :=
  (eraseTerm seedVar p.1, eraseTerm seedVar p.2)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Pointwise erasure of a finite equation system. -/
def eraseTermPairs {L : Language} (seedVar : Nat)
    (pairs : List
      (Term (FreshGroundLanguage L) × Term (FreshGroundLanguage L))) :
    List (Term L × Term L) :=
  pairs.map (eraseTermPair seedVar)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- On an original atom, total erasure agrees with certified descent. -/
theorem eraseAtom_eq_lowerAtom {L : Language} (hNoEq : L.withoutEquality)
    (seedVar : Nat)
    {atom : FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (h : IsOriginalAtom (hNoEq := by first | exact hNoEq | done) atom) :
    eraseAtom (hNoEq := by first | exact hNoEq | done) seedVar atom = lowerAtom (hNoEq := by first | exact hNoEq | done) atom h := by
  cases atom with
  | predN P args =>
      simp only [eraseAtom, lowerAtom]
      congr 1
      funext i
      exact eraseTerm_eq_lowerTerm seedVar (h i)
  | eq_ hEq lhs rhs =>
      simp only [eraseAtom, lowerAtom]
      congr 1
      · exact eraseTerm_eq_lowerTerm seedVar h.1
      · exact eraseTerm_eq_lowerTerm seedVar h.2

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- On an original literal, total erasure agrees with certified descent. -/
theorem eraseLiteral_eq_lowerLiteral {L : Language} (hNoEq : L.withoutEquality)
    (seedVar : Nat)
    {lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (h : IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit) :
    eraseLiteral (hNoEq := by first | exact hNoEq | done) seedVar lit = lowerLiteral (hNoEq := by first | exact hNoEq | done) lit h := by
  cases lit <;>
    exact congrArg _ (eraseAtom_eq_lowerAtom (hNoEq := by first | exact hNoEq | done) seedVar h)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- On an original clause, total erasure agrees with certified descent. -/
theorem eraseClause_eq_lowerClause {L : Language} (hNoEq : L.withoutEquality)
    (seedVar : Nat)
    {C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (h : IsOriginalClause (hNoEq := by first | exact hNoEq | done) C) :
    eraseClause (hNoEq := by first | exact hNoEq | done) seedVar C = lowerClause (hNoEq := by first | exact hNoEq | done) C h := by
  induction h with
  | nil =>
      rfl
  | cons hlit hrest ih =>
      change
        eraseLiteral (hNoEq := by first | exact hNoEq | done) seedVar _ :: eraseClause (hNoEq := by first | exact hNoEq | done) seedVar _ =
          lowerLiteral (hNoEq := by first | exact hNoEq | done) _ _ :: lowerClause (hNoEq := by first | exact hNoEq | done) _ _
      rw [eraseLiteral_eq_lowerLiteral (hNoEq := by first | exact hNoEq | done) seedVar hlit, ih]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Erasing two atoms before per-position equation extraction is the same as
    erasing every extracted equation endpoint. -/
theorem atomUnifPairs?_eraseAtom {L : Language} (hNoEq : L.withoutEquality)
    (seedVar : Nat)
    (reference atom : FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) :
    atomUnifPairs? (hNoEq := by first | exact hNoEq | done) (eraseAtom (hNoEq := by first | exact hNoEq | done) seedVar reference) (eraseAtom (hNoEq := by first | exact hNoEq | done) seedVar atom) =
      Option.map (eraseTermPairs seedVar)
        (atomUnifPairs? (hNoEq := by first | exact hNoEq | done) reference atom) := by
  classical
  cases reference with
  | predN P referenceArgs =>
      cases atom with
      | predN Q args =>
          by_cases h : P = Q
          · subst Q
            change (if P = P then some (List.ofFn (fun i =>
                (eraseTerm seedVar (referenceArgs i), eraseTerm seedVar (args i)))) else none) =
              Option.map (eraseTermPairs seedVar)
                (if P = P then some (List.ofFn (fun i => (referenceArgs i, args i))) else none)
            simp only [ite_true, Option.map_some, eraseTermPairs, List.map_ofFn]
            congr 1
          · simp only [eraseAtom, atomUnifPairs?]
            rw [dif_neg h]
            split
            next hEq => exact (h hEq).elim
            next => rfl
      | eq_ =>
          rfl
  | eq_ =>
      cases atom <;> rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Literal payload extraction commutes with total erasure. -/
theorem literalAtom_eraseLiteral {L : Language} (hNoEq : L.withoutEquality)
    (seedVar : Nat)
    (lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) :
    literalAtom (hNoEq := by first | exact hNoEq | done) (eraseLiteral (hNoEq := by first | exact hNoEq | done) seedVar lit) =
      eraseAtom (hNoEq := by first | exact hNoEq | done) seedVar (literalAtom (hNoEq := by first | exact hNoEq | done) lit) := by
  cases lit <;> rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Reference-based literal equation extraction commutes with total erasure. -/
theorem litSetUnifPairsAgainst_eraseClause {L : Language} (hNoEq : L.withoutEquality)
    (seedVar : Nat)
    (reference : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (rest : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) :
    litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) (eraseLiteral (hNoEq := by first | exact hNoEq | done) seedVar reference)
        (eraseClause (hNoEq := by first | exact hNoEq | done) seedVar rest) =
      Option.map (eraseTermPairs seedVar)
        (litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) reference rest) := by
  induction rest with
  | nil =>
      rfl
  | cons lit tail ih =>
      change
        litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) (eraseLiteral (hNoEq := by first | exact hNoEq | done) seedVar reference)
            (eraseLiteral (hNoEq := by first | exact hNoEq | done) seedVar lit :: eraseClause (hNoEq := by first | exact hNoEq | done) seedVar tail) =
          Option.map (eraseTermPairs seedVar)
            (litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) reference (lit :: tail))
      simp only [litSetUnifPairsAgainst, literalAtom_eraseLiteral (hNoEq := by first | exact hNoEq | done)]
      rw [atomUnifPairs?_eraseAtom (hNoEq := by first | exact hNoEq | done), ih]
      cases atomUnifPairs? (hNoEq := by first | exact hNoEq | done) (literalAtom (hNoEq := by first | exact hNoEq | done) reference) (literalAtom (hNoEq := by first | exact hNoEq | done) lit) <;>
        cases litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) reference tail <;>
        simp [eraseTermPairs]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Full literal-set equation extraction commutes with total erasure. -/
theorem litSetUnifPairs_eraseClause {L : Language} (hNoEq : L.withoutEquality)
    (seedVar : Nat)
    (lits : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) :
    litSetUnifPairs (hNoEq := by first | exact hNoEq | done) (eraseClause (hNoEq := by first | exact hNoEq | done) seedVar lits) =
      Option.map (eraseTermPairs seedVar) (litSetUnifPairs (hNoEq := (FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) lits) := by
  cases lits with
  | nil =>
      rfl
  | cons reference rest =>
      simp only [eraseClause, List.map_cons, litSetUnifPairs,
        literalAtom_eraseLiteral (hNoEq := by first | exact hNoEq | done)]
      cases hAtom : literalAtom (hNoEq := by first | exact hNoEq | done) reference with
      | predN =>
          simp only [eraseAtom]
          exact litSetUnifPairsAgainst_eraseClause (hNoEq := by first | exact hNoEq | done)
            seedVar reference rest
      | eq_ =>
          simp [eraseAtom]

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Certified literal-set descent transports a successful equation extraction
    to the erased pair system. -/
theorem litSetUnifPairs_lowerClause {L : Language} (hNoEq : L.withoutEquality)
    (seedVar : Nat)
    {lits : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hLits : IsOriginalClause (hNoEq := by first | exact hNoEq | done) lits)
    {pairs : List
      (Term (FreshGroundLanguage L) × Term (FreshGroundLanguage L))}
    (hPairs : litSetUnifPairs (hNoEq := (FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) lits = some pairs) :
    litSetUnifPairs (hNoEq := by first | exact hNoEq | done) (lowerClause (hNoEq := by first | exact hNoEq | done) lits hLits) =
      some (eraseTermPairs seedVar pairs) := by
  rw [← eraseClause_eq_lowerClause (hNoEq := by first | exact hNoEq | done) seedVar hLits,
    litSetUnifPairs_eraseClause (hNoEq := by first | exact hNoEq | done), hPairs]
  rfl

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Literal payload extraction preserves an original-symbol certificate. -/
theorem literalAtom_isOriginal {L : Language} (hNoEq : L.withoutEquality)
    {lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (h : IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit) :
    IsOriginalAtom (hNoEq := by first | exact hNoEq | done) (literalAtom (hNoEq := by first | exact hNoEq | done) lit) := by
  cases lit <;> exact h

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Every endpoint returned by atom equation extraction came from one of the
    two original-symbol atoms. -/
theorem atomUnifPairs_isOriginal {L : Language} (hNoEq : L.withoutEquality)
    {reference atom : FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    {pairs : List
      (Term (FreshGroundLanguage L) × Term (FreshGroundLanguage L))}
    (hReference : IsOriginalAtom (hNoEq := by first | exact hNoEq | done) reference)
    (hAtom : IsOriginalAtom (hNoEq := by first | exact hNoEq | done) atom)
    (hPairs : atomUnifPairs? (hNoEq := by first | exact hNoEq | done) reference atom = some pairs) :
    ∀ p ∈ pairs, IsOriginalTerm p.1 ∧ IsOriginalTerm p.2 := by
  cases reference with
  | predN P referenceArgs =>
      cases atom with
      | predN Q args =>
          simp only [atomUnifPairs?] at hPairs
          split at hPairs
          next hPQ =>
            subst Q
            simp only [Option.some.injEq] at hPairs
            subst pairs
            intro p hp
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
            exact ⟨hReference i, hAtom i⟩
          next =>
            simp at hPairs
      | eq_ =>
          simp [atomUnifPairs?] at hPairs
  | eq_ =>
      cases atom <;> simp [atomUnifPairs?] at hPairs

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Equation extraction against one reference literal preserves the
    original-symbol provenance of every endpoint. -/
theorem litSetUnifPairsAgainst_isOriginal {L : Language} (hNoEq : L.withoutEquality)
    {reference : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    {rest : List (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))}
    {pairs : List
      (Term (FreshGroundLanguage L) × Term (FreshGroundLanguage L))}
    (hReference : IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) reference)
    (hRest : ∀ lit ∈ rest, IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit)
    (hPairs : litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) reference rest = some pairs) :
    ∀ p ∈ pairs, IsOriginalTerm p.1 ∧ IsOriginalTerm p.2 := by
  induction rest generalizing pairs with
  | nil =>
      simp only [litSetUnifPairsAgainst, Option.some.injEq] at hPairs
      subst pairs
      intro p hp
      exact (List.not_mem_nil hp).elim
  | cons lit tail ih =>
      simp only [litSetUnifPairsAgainst] at hPairs
      cases hHeadPairs : atomUnifPairs? (hNoEq := by first | exact hNoEq | done)
          (literalAtom (hNoEq := by first | exact hNoEq | done) reference) (literalAtom (hNoEq := by first | exact hNoEq | done) lit) with
      | none =>
          simp [hHeadPairs] at hPairs
      | some headPairs =>
          cases hTailPairs : litSetUnifPairsAgainst (hNoEq := by first | exact hNoEq | done) reference tail with
          | none =>
              simp [hHeadPairs, hTailPairs] at hPairs
          | some tailPairs =>
              simp [hHeadPairs, hTailPairs] at hPairs
              subst pairs
              intro p hp
              rcases List.mem_append.mp hp with hp | hp
              · exact atomUnifPairs_isOriginal (hNoEq := by first | exact hNoEq | done)
                  (literalAtom_isOriginal (hNoEq := by first | exact hNoEq | done) hReference)
                  (literalAtom_isOriginal (hNoEq := by first | exact hNoEq | done)
                    (hRest lit List.mem_cons_self))
                  hHeadPairs p hp
              · exact ih
                  (fun x hx => hRest x (List.mem_cons_of_mem lit hx))
                  hTailPairs p hp

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The equation system extracted from an original-symbol literal list is
    itself an original-symbol pair system. -/
theorem litSetUnifPairs_isOriginal {L : Language} (hNoEq : L.withoutEquality)
    {lits : List (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))}
    {pairs : List
      (Term (FreshGroundLanguage L) × Term (FreshGroundLanguage L))}
    (hLits : ∀ lit ∈ lits, IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit)
    (hPairs : litSetUnifPairs (hNoEq := (FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) lits = some pairs) :
    IsOriginalPairSystem pairs := by
  cases lits with
  | nil =>
      simp [litSetUnifPairs] at hPairs
  | cons reference rest =>
      have hReference := hLits reference List.mem_cons_self
      have hRest : ∀ lit ∈ rest, IsOriginalLiteral (hNoEq := by first | exact hNoEq | done) lit :=
        fun lit hMem => hLits lit (List.mem_cons_of_mem reference hMem)
      simp only [litSetUnifPairs] at hPairs
      cases hAtom : literalAtom (hNoEq := by first | exact hNoEq | done) reference with
      | predN =>
          simp only [hAtom] at hPairs
          exact litSetUnifPairsAgainst_isOriginal (hNoEq := by first | exact hNoEq | done)
            hReference hRest hPairs
      | eq_ =>
          simp [hAtom] at hPairs

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- An MGU of an original-symbol equation system cannot introduce the fresh
    constant in any of its images.  Erasing the MGU and lifting the result
    gives an original-valued alternate unifier; most-generality factors it
    through the given MGU, after which `IsOriginalTerm.of_subst` rules out a
    fresh constant already present in an MGU image. -/
theorem isPairwiseMGU_isOriginalSubst {L : Language}
    {sigma : Nat → Term (FreshGroundLanguage L)}
    {pairs : List
      (Term (FreshGroundLanguage L) × Term (FreshGroundLanguage L))}
    (hPairs : IsOriginalPairSystem pairs)
    (hMGU : IsPairwiseMGU sigma pairs) :
    IsOriginalSubst sigma := by
  let erased : Nat → Term L := eraseSubst 0 sigma
  let repaired : Nat → Term (FreshGroundLanguage L) := liftSubst erased
  have hRepairedUnifier : IsPairwiseUnifier repaired pairs := by
    intro p hp
    obtain ⟨hLeft, hRight⟩ := hPairs p hp
    have hErased := congrArg (eraseTerm 0) (hMGU.1 p hp)
    rw [← liftTerm_lowerTerm hLeft, ← liftTerm_lowerTerm hRight] at hErased
    have hBase :
        termSubstAll (lowerTerm p.1 hLeft) erased =
          termSubstAll (lowerTerm p.2 hRight) erased := by
      change
        termSubstAll (lowerTerm p.1 hLeft)
            (fun x => eraseTerm 0 (sigma x)) =
          termSubstAll (lowerTerm p.2 hRight)
            (fun x => eraseTerm 0 (sigma x))
      simpa only [eraseTerm_termSubstAll_liftTerm] using hErased
    rw [← liftTerm_lowerTerm hLeft, ← liftTerm_lowerTerm hRight]
    change
      termSubstAll (liftTerm (lowerTerm p.1 hLeft))
          (liftSubst erased) =
        termSubstAll (liftTerm (lowerTerm p.2 hRight))
          (liftSubst erased)
    rw [← liftTerm_termSubstAll, ← liftTerm_termSubstAll]
    exact congrArg liftTerm hBase
  obtain ⟨theta, hFactor⟩ := hMGU.2.2 repaired hRepairedUnifier
  intro x
  apply IsOriginalTerm.of_subst (sigma x) theta
  change IsOriginalTerm (SubstitutionCore.substCompose theta sigma x)
  rw [← hFactor x]
  exact liftTerm_isOriginal (erased x)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Erasing an original-symbol pairwise MGU yields a pairwise MGU of the
    erased equation system.  Factorizations descend by erasing the
    extension-language factor substitution. -/
theorem isPairwiseMGU_erase {L : Language}
    (seedVar : Nat)
    {sigma : Nat → Term (FreshGroundLanguage L)}
    {pairs : List
      (Term (FreshGroundLanguage L) × Term (FreshGroundLanguage L))}
    (hPairs : IsOriginalPairSystem pairs)
    (hMGU : IsPairwiseMGU sigma pairs) :
    IsPairwiseMGU (eraseSubst seedVar sigma)
      (eraseTermPairs seedVar pairs) := by
  have hSigma : IsOriginalSubst sigma :=
    isPairwiseMGU_isOriginalSubst hPairs hMGU
  refine ⟨?_, ?_, ?_⟩
  · intro p hMem
    obtain ⟨source, hSourceMem, rfl⟩ :=
      List.mem_map.mp hMem
    obtain ⟨hLeft, hRight⟩ := hPairs source hSourceMem
    have hEq := congrArg (eraseTerm seedVar)
      (hMGU.1 source hSourceMem)
    rw [eraseTerm_termSubstAll_of_original seedVar hLeft sigma,
      eraseTerm_termSubstAll_of_original seedVar hRight sigma] at hEq
    exact hEq
  · intro x hx
    have hxExtension : SubstitutionCore.substSupport sigma x := by
      intro hIdentity
      apply hx
      change eraseTerm seedVar (sigma x) = Term.var x
      rw [hIdentity]
      rfl
    obtain ⟨source, hSourceMem, hLeft | hRight⟩ :=
      hMGU.2.1 x hxExtension
    · refine ⟨eraseTermPair seedVar source,
        List.mem_map.mpr ⟨source, hSourceMem, rfl⟩, Or.inl ?_⟩
      change termFV (eraseTerm seedVar source.1) x
      rw [termFV_eraseTerm_of_original seedVar
        (hPairs source hSourceMem).1]
      exact hLeft
    · refine ⟨eraseTermPair seedVar source,
        List.mem_map.mpr ⟨source, hSourceMem, rfl⟩, Or.inr ?_⟩
      change termFV (eraseTerm seedVar source.2) x
      rw [termFV_eraseTerm_of_original seedVar
        (hPairs source hSourceMem).2]
      exact hRight
  · intro tau hTau
    have hLiftTau : IsPairwiseUnifier (liftSubst tau) pairs := by
      intro source hSourceMem
      obtain ⟨hLeft, hRight⟩ := hPairs source hSourceMem
      rw [← liftTerm_lowerTerm hLeft, ← liftTerm_lowerTerm hRight,
        ← liftTerm_termSubstAll, ← liftTerm_termSubstAll]
      apply congrArg liftTerm
      have hErased := hTau (eraseTermPair seedVar source)
        (List.mem_map.mpr ⟨source, hSourceMem, rfl⟩)
      change
        termSubstAll (eraseTerm seedVar source.1) tau =
          termSubstAll (eraseTerm seedVar source.2) tau at hErased
      rw [eraseTerm_eq_lowerTerm seedVar hLeft,
        eraseTerm_eq_lowerTerm seedVar hRight] at hErased
      exact hErased
    obtain ⟨theta, hFactor⟩ := hMGU.2.2 (liftSubst tau) hLiftTau
    refine ⟨eraseSubst seedVar theta, ?_⟩
    intro x
    have hErasedFactor :=
      congrArg (eraseTerm seedVar) (hFactor x)
    change
      eraseTerm seedVar (liftSubst tau x) =
        eraseTerm seedVar (termSubstAll (sigma x) theta)
      at hErasedFactor
    rw [eraseTerm_termSubstAll_of_original seedVar (hSigma x) theta]
      at hErasedFactor
    simpa only [liftSubst, eraseSubst, eraseTerm_liftTerm, SubstitutionCore.substCompose] using
      hErasedFactor

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Both substitutions of a separating pair are original-valued.  On the
    respective clause variables they are variable renamings, and away from
    those variables the support clauses force the identity substitution. -/
theorem IsSeparatingPair.isOriginalSubsts {L : Language} (hNoEq : L.withoutEquality)
    {rho rho' : Nat → Term (FreshGroundLanguage L)}
    {A A' : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (h : IsSeparatingPair (hNoEq := by first | exact hNoEq | done) rho rho' A A') :
    IsOriginalSubst rho ∧ IsOriginalSubst rho' := by
  obtain ⟨hVar, hVar', _, _, _, hOutside, hOutside'⟩ := h
  constructor
  · intro x
    by_cases hx : clauseFV (hNoEq := by first | exact hNoEq | done) A x
    · obtain ⟨y, hy⟩ := hVar x hx
      rw [hy]
      exact .var y
    · rw [hOutside x hx]
      exact .var x
  · intro x
    by_cases hx : clauseFV (hNoEq := by first | exact hNoEq | done) A' x
    · obtain ⟨y, hy⟩ := hVar' x hx
      rw [hy]
      exact .var y
    · rw [hOutside' x hx]
      exact .var x

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- A resolvent certificate over original parent clauses forces every stored
    witness needed by certified descent to use only original symbols. -/
theorem IsResolventVia.isOriginalWitnesses {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    {C A B : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    {A' B' : List (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))}
    {rho rho' sigma : Nat → Term (FreshGroundLanguage L)}
    (hVia : IsResolventVia (hNoEq := by first | exact hNoEq | done) C A B A' B' rho rho' sigma)
    (hA : IsOriginalClause (hNoEq := by first | exact hNoEq | done) A)
    (hB : IsOriginalClause (hNoEq := by first | exact hNoEq | done) B) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) A' ∧
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) B' ∧
    IsOriginalSubst rho ∧
    IsOriginalSubst rho' ∧
    IsOriginalSubst sigma := by
  obtain ⟨hSubA, hSubB, _, _, _, _, _, hSeparating,
    ⟨pairs, hPairs, _, hMGU⟩, _⟩ := hVia
  have hA' : IsOriginalClause (hNoEq := by first | exact hNoEq | done) A' :=
    hA.of_sublist (hNoEq := by first | exact hNoEq | done) hSubA
  have hB' : IsOriginalClause (hNoEq := by first | exact hNoEq | done) B' :=
    hB.of_sublist (hNoEq := by first | exact hNoEq | done) hSubB
  obtain ⟨hRho, hRho'⟩ :=
    IsSeparatingPair.isOriginalSubsts (hNoEq := by first | exact hNoEq | done) hSeparating
  have hUnified :
      IsOriginalClause (hNoEq := by first | exact hNoEq | done)
        (LitSetAbs (hNoEq := by first | exact hNoEq | done)
          (substLits (hNoEq := by first | exact hNoEq | done) rho A' ++
            substLits (hNoEq := by first | exact hNoEq | done) rho' (LitSetConjugate (hNoEq := by first | exact hNoEq | done) B'))) :=
    ((hA'.subst (hNoEq := by first | exact hNoEq | done) rho hRho).append (hNoEq := by first | exact hNoEq | done)
      (hB'.conjugate.subst (hNoEq := by first | exact hNoEq | done) rho' hRho')).abs
  have hPairOriginal : IsOriginalPairSystem pairs :=
    litSetUnifPairs_isOriginal (hNoEq := by first | exact hNoEq | done)
      (fun lit hMem => hUnified.literal_of_mem (hNoEq := by first | exact hNoEq | done) hMem) hPairs
  exact ⟨hA', hB', hRho, hRho',
    isPairwiseMGU_isOriginalSubst hPairOriginal hMGU⟩

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Certified descent transports a complete resolvent witness from the fresh
    extension back to the base language. -/
theorem IsResolventVia.lower {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    {C A B A' B' : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    {rho rho' sigma : Nat → Term (FreshGroundLanguage L)}
    (hVia : IsResolventVia (hNoEq := by first | exact hNoEq | done) C A B A' B' rho rho' sigma)
    (hC : IsOriginalClause (hNoEq := by first | exact hNoEq | done) C)
    (hA : IsOriginalClause (hNoEq := by first | exact hNoEq | done) A)
    (hB : IsOriginalClause (hNoEq := by first | exact hNoEq | done) B)
    (hA' : IsOriginalClause (hNoEq := by first | exact hNoEq | done) A')
    (hB' : IsOriginalClause (hNoEq := by first | exact hNoEq | done) B')
    (hRho : IsOriginalSubst rho)
    (hRho' : IsOriginalSubst rho')
    (hSigma : IsOriginalSubst sigma) :
    IsResolventVia (hNoEq := by first | exact hNoEq | done)
      (lowerClause (hNoEq := by first | exact hNoEq | done) C hC)
      (lowerClause (hNoEq := by first | exact hNoEq | done) A hA)
      (lowerClause (hNoEq := by first | exact hNoEq | done) B hB)
      (lowerClause (hNoEq := by first | exact hNoEq | done) A' hA')
      (lowerClause (hNoEq := by first | exact hNoEq | done) B' hB')
      (lowerSubst rho hRho)
      (lowerSubst rho' hRho')
      (lowerSubst sigma hSigma) := by
  obtain ⟨hSubA, hSubB, hA'Ne, hB'Ne, hSameSign, hOpposite,
    hSamePred, hSeparating, ⟨pairs, hPairExtraction, hUnifier, hMGU⟩,
    hConclusion⟩ := hVia
  have hUnified :
      IsOriginalClause (hNoEq := by first | exact hNoEq | done)
        (LitSetAbs (hNoEq := by first | exact hNoEq | done)
          (substLits (hNoEq := by first | exact hNoEq | done) rho A' ++
            substLits (hNoEq := by first | exact hNoEq | done) rho' (LitSetConjugate (hNoEq := by first | exact hNoEq | done) B'))) :=
    ((hA'.subst (hNoEq := by first | exact hNoEq | done) rho hRho).append (hNoEq := by first | exact hNoEq | done)
      (hB'.conjugate.subst (hNoEq := by first | exact hNoEq | done) rho' hRho')).abs
  have hPairOriginal : IsOriginalPairSystem pairs :=
    litSetUnifPairs_isOriginal (hNoEq := by first | exact hNoEq | done)
      (fun lit hMem => hUnified.literal_of_mem (hNoEq := by first | exact hNoEq | done) hMem)
      hPairExtraction
  have hLowerUnified :
      lowerClause (hNoEq := by first | exact hNoEq | done)
          (LitSetAbs (hNoEq := by first | exact hNoEq | done)
            (substLits (hNoEq := by first | exact hNoEq | done) rho A' ++
              substLits (hNoEq := by first | exact hNoEq | done) rho' (LitSetConjugate (hNoEq := by first | exact hNoEq | done) B')))
          hUnified =
        LitSetAbs (hNoEq := by first | exact hNoEq | done)
          (substLits (hNoEq := by first | exact hNoEq | done) (lowerSubst rho hRho) (lowerClause (hNoEq := by first | exact hNoEq | done) A' hA') ++
            substLits (hNoEq := by first | exact hNoEq | done) (lowerSubst rho' hRho')
              (LitSetConjugate (hNoEq := by first | exact hNoEq | done) (lowerClause (hNoEq := by first | exact hNoEq | done) B' hB'))) := by
    apply liftClause_injective (hNoEq := by first | exact hNoEq | done)
    rw [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_abs (hNoEq := by first | exact hNoEq | done), liftClause_append (hNoEq := by first | exact hNoEq | done),
      liftClause_substLits (hNoEq := by first | exact hNoEq | done), liftSubst_lowerSubst,
      liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_substLits (hNoEq := by first | exact hNoEq | done),
      liftSubst_lowerSubst, liftClause_conjugate (hNoEq := by first | exact hNoEq | done),
      liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)]
  have hLowerExtraction :=
    litSetUnifPairs_lowerClause (hNoEq := by first | exact hNoEq | done) 0 hUnified hPairExtraction
  rw [hLowerUnified] at hLowerExtraction
  have hLowerMGU :=
    isPairwiseMGU_erase 0 hPairOriginal hMGU
  rw [eraseSubst_eq_lowerSubst 0 sigma hSigma] at hLowerMGU
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply isSublist_of_liftClause (hNoEq := by first | exact hNoEq | done)
    simpa only [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)] using hSubA
  · apply isSublist_of_liftClause (hNoEq := by first | exact hNoEq | done)
    simpa only [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)] using hSubB
  · intro hEmpty
    apply hA'Ne
    rw [← liftClause_lowerClause (hNoEq := by first | exact hNoEq | done) hA', hEmpty]
    rfl
  · intro hEmpty
    apply hB'Ne
    rw [← liftClause_lowerClause (hNoEq := by first | exact hNoEq | done) hB', hEmpty]
    rfl
  · apply litSetSameSign_of_liftClause (hNoEq := by first | exact hNoEq | done)
    simpa only [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)] using hSameSign
  · apply litSetOppositeSign_of_liftClause (hNoEq := by first | exact hNoEq | done)
    simpa only [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)] using hOpposite
  · apply litSetSamePred_of_liftClause (hNoEq := by first | exact hNoEq | done)
    simpa only [liftClause_append (hNoEq := by first | exact hNoEq | done), liftClause_lowerClause (hNoEq := by first | exact hNoEq | done),
      liftClause_conjugate (hNoEq := by first | exact hNoEq | done)] using hSamePred
  · apply isSeparatingPair_of_lift (hNoEq := by first | exact hNoEq | done)
    simpa only [liftSubst_lowerSubst, liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)] using
      hSeparating
  · exact ⟨eraseTermPairs 0 pairs, hLowerExtraction,
      hLowerMGU.1, hLowerMGU⟩
  · intro lit
    rw [← liftLiteral_mem_liftClause_iff hNoEq lit _,
      ← liftLiteral_mem_liftClause_iff hNoEq lit _]
    rw [liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_substLits (hNoEq := by first | exact hNoEq | done),
      liftSubst_lowerSubst, liftClause_append (hNoEq := by first | exact hNoEq | done),
      liftClause_substLits (hNoEq := by first | exact hNoEq | done), liftSubst_lowerSubst,
      liftClause_listDiff (hNoEq := by first | exact hNoEq | done), liftClause_lowerClause (hNoEq := by first | exact hNoEq | done),
      liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_substLits (hNoEq := by first | exact hNoEq | done),
      liftSubst_lowerSubst, liftClause_listDiff (hNoEq := by first | exact hNoEq | done),
      liftClause_lowerClause (hNoEq := by first | exact hNoEq | done), liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)]
    exact hConclusion _

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- The constant substitution sending every variable to the fresh seed. -/
def seedSubst {L : Language} :
    Nat → Term (FreshGroundLanguage L) :=
  fun _ => seed



-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Substitution by the fresh seed removes every term variable. -/
theorem termVars_termSubstAll_seed {L : Language}
    (t : Term (FreshGroundLanguage L)) :
    termVars (termSubstAll t seedSubst) = Set.empty := by
  induction t with
  | var x =>
      rfl
  | const c =>
      rfl
  | func f args ih =>
      ext x
      constructor
      · rintro ⟨i, hi⟩
        rw [ih i] at hi
        exact hi
      · intro h
        exact h.elim

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Every atom instantiated by the seed substitution is variable-free. -/
theorem atomVars_subst_seed {L : Language} (hNoEq : L.withoutEquality)
    (atom : FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) :
    (atom.subst (hNoEq := by first | exact hNoEq | done) seedSubst).vars = Set.empty := by
  cases atom with
  | predN P args =>
      ext x
      constructor
      · rintro ⟨i, hi⟩
        rw [termVars_termSubstAll_seed] at hi
        exact hi
      · intro h
        exact h.elim
  | eq_ hL lhs rhs =>
      ext x
      constructor
      · intro h
        rcases h with h | h
        · rw [termVars_termSubstAll_seed] at h
          exact h
        · rw [termVars_termSubstAll_seed] at h
          exact h
      · intro h
        exact h.elim

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Every literal instantiated by the seed substitution is variable-free. -/
theorem literalVars_subst_seed {L : Language} (hNoEq : L.withoutEquality)
    (lit : FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) :
    (substLit (hNoEq := by first | exact hNoEq | done) seedSubst lit).vars = Set.empty := by
  cases lit <;> exact atomVars_subst_seed (hNoEq := by first | exact hNoEq | done) _

-- retained: used by LCS.FOResolution.Method.HerbrandBridge
/-- Seed substitution turns every clause in the extension into a ground
    clause; in particular it grounds every lifted base-language clause. -/
theorem substLits_seed_isGround {L : Language} (hNoEq : L.withoutEquality)
    (C : FOClause (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) :
    FOClause.isGround (L := FreshGroundLanguage L) hNoEq (substLits (hNoEq := by first | exact hNoEq | done) seedSubst C) := by
  unfold FOClause.isGround
  ext x
  constructor
  · rintro ⟨lit, hlit, hx⟩
    simp only [substLits, List.mem_map] at hlit
    obtain ⟨source, hsource, rfl⟩ := hlit
    change FOLiteral.vars _ (substLit _ seedSubst source) x at hx
    rw [literalVars_subst_seed (hNoEq := by first | exact hNoEq | done)] at hx
    exact hx
  · intro h
    exact h.elim

-- ATTACH-BLOCKER: private declaration
/-- Adversarial regression: a lifted base term round-trips, while the fresh
    seed is provably outside the certified descent domain. -/
private example {L : Language} (t : Term L) :
    lowerTerm (liftTerm t) (liftTerm_isOriginal t) = t ∧
      ¬ IsOriginalTerm (@seed L) :=
  ⟨lowerTerm_liftTerm t, seed_not_original⟩

end FreshGroundLanguage
end LCS.FOResolution.Method
end

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification
namespace FOResolutionTree
open FreshGroundLanguage

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- Structural invariant certifying that every clause and substitution stored
    in a fresh-extension resolution tree uses only original symbols. -/
def AllOriginal {L : Language} (hNoEq : L.withoutEquality) :
    FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) → Prop
  | .axiom_ C =>
      IsOriginalClause (hNoEq := by first | exact hNoEq | done) C
  | .resolve T₁ T₂ resolvedA resolvedB rho rho' sigma =>
      AllOriginal (hNoEq := by first | exact hNoEq | done) T₁ ∧
      AllOriginal (hNoEq := by first | exact hNoEq | done) T₂ ∧
      IsOriginalClause (hNoEq := by first | exact hNoEq | done) resolvedA ∧
      IsOriginalClause (hNoEq := by first | exact hNoEq | done) resolvedB ∧
      IsOriginalSubst rho ∧
      IsOriginalSubst rho' ∧
      IsOriginalSubst sigma

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Certified structural descent of a fresh-extension resolution tree. -/
def lower {L : Language} (hNoEq : L.withoutEquality) :
    (T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)) →
      AllOriginal (hNoEq := by first | exact hNoEq | done) T → FOResolutionTree L hNoEq
  | .axiom_ C, hC =>
      .axiom_ (lowerClause (hNoEq := by first | exact hNoEq | done) C hC)
  | .resolve T₁ T₂ resolvedA resolvedB rho rho' sigma,
      ⟨h₁, h₂, hA, hB, hRho, hRho', hSigma⟩ =>
      .resolve
        (lower (hNoEq := by first | exact hNoEq | done) T₁ h₁)
        (lower (hNoEq := by first | exact hNoEq | done) T₂ h₂)
        (lowerClause (hNoEq := by first | exact hNoEq | done) resolvedA hA)
        (lowerClause (hNoEq := by first | exact hNoEq | done) resolvedB hB)
        (lowerSubst rho hRho)
        (lowerSubst rho' hRho')
        (lowerSubst sigma hSigma)

-- ATTACH-BLOCKER: dependency: retained front declaration references this helper
/-- The label of a certified lowered tree lifts back to the source label. -/
theorem liftClause_lower_label {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    (T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (hT : AllOriginal (hNoEq := by first | exact hNoEq | done) T) :
    liftClause (hNoEq := by first | exact hNoEq | done) (label (hNoEq := by first | exact hNoEq | done) (lower (hNoEq := by first | exact hNoEq | done) T hT)) = label (hNoEq := by first | exact hNoEq | done) T := by
  induction T with
  | axiom_ C =>
      exact liftClause_lowerClause (hNoEq := by first | exact hNoEq | done) hT
  | resolve T₁ T₂ resolvedA resolvedB rho rho' sigma ih₁ ih₂ =>
      obtain ⟨h₁, h₂, hA, hB, hRho, hRho', hSigma⟩ := hT
      simp only [lower, label]
      rw [liftClause_substLits (hNoEq := by first | exact hNoEq | done), liftSubst_lowerSubst,
        liftClause_append (hNoEq := by first | exact hNoEq | done), liftClause_substLits (hNoEq := by first | exact hNoEq | done),
        liftSubst_lowerSubst, liftClause_listDiff (hNoEq := by first | exact hNoEq | done),
        ih₁ h₁, liftClause_lowerClause (hNoEq := by first | exact hNoEq | done),
        liftClause_substLits (hNoEq := by first | exact hNoEq | done), liftSubst_lowerSubst,
        liftClause_listDiff (hNoEq := by first | exact hNoEq | done), ih₂ h₂, liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Every label of an all-original tree is an original-symbol clause. -/
theorem AllOriginal.label {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    {T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hT : AllOriginal (hNoEq := by first | exact hNoEq | done) T) :
    IsOriginalClause (hNoEq := by first | exact hNoEq | done) (label (hNoEq := by first | exact hNoEq | done) T) := by
  rw [← liftClause_lower_label (hNoEq := by first | exact hNoEq | done) T hT]
  exact liftClause_isOriginal (hNoEq := by first | exact hNoEq | done) _

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Certified descent computes exactly the certified descent of the source
    root label. -/
theorem lower_label {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    (T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (hT : AllOriginal (hNoEq := by first | exact hNoEq | done) T) :
    label (hNoEq := by first | exact hNoEq | done) (lower (hNoEq := by first | exact hNoEq | done) T hT) =
      lowerClause (hNoEq := by first | exact hNoEq | done) (label (hNoEq := by first | exact hNoEq | done) T) (hT.label (hNoEq := by first | exact hNoEq | done)) := by
  apply liftClause_injective (hNoEq := by first | exact hNoEq | done)
  rw [liftClause_lower_label (hNoEq := by first | exact hNoEq | done), liftClause_lowerClause (hNoEq := by first | exact hNoEq | done)]

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
/-- Original leaves and a well-formed resolution certificate force every
    stored witness in the tree to be original. -/
theorem AllOriginal.of_wellFormed {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    {T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hLeaves : leavesFrom (hNoEq := by first | exact hNoEq | done) T (IsOriginalClause (hNoEq := by first | exact hNoEq | done)))
    (hWF : isWellFormed (hNoEq := by first | exact hNoEq | done) T) :
    AllOriginal (hNoEq := by first | exact hNoEq | done) T := by
  induction T with
  | axiom_ =>
      exact hLeaves
  | resolve T₁ T₂ resolvedA resolvedB rho rho' sigma ih₁ ih₂ =>
      obtain ⟨hLeaves₁, hLeaves₂⟩ := hLeaves
      obtain ⟨hWF₁, hWF₂, hVia⟩ := hWF
      have h₁ := ih₁ hLeaves₁ hWF₁
      have h₂ := ih₂ hLeaves₂ hWF₂
      obtain ⟨hA, hB, hRho, hRho', hSigma⟩ :=
        FreshGroundLanguage.IsResolventVia.isOriginalWitnesses (hNoEq := hNoEq)
          hVia (AllOriginal.label (hNoEq := by first | exact hNoEq | done) h₁) (AllOriginal.label (hNoEq := by first | exact hNoEq | done) h₂)
      exact ⟨h₁, h₂, hA, hB, hRho, hRho', hSigma⟩

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Certified tree descent preserves every well-formed resolution witness. -/
theorem lower_isWellFormed {L : Language} (hNoEq : L.withoutEquality)
    [DecidableEq (FOLiteral L hNoEq)]
    [DecidableEq (FOLiteral (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))]
    (T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq))
    (hOriginal : AllOriginal (hNoEq := by first | exact hNoEq | done) T)
    (hWF : isWellFormed (hNoEq := by first | exact hNoEq | done) T) :
    isWellFormed (hNoEq := by first | exact hNoEq | done) (lower (hNoEq := by first | exact hNoEq | done) T hOriginal) := by
  induction T with
  | axiom_ =>
      trivial
  | resolve T₁ T₂ resolvedA resolvedB rho rho' sigma ih₁ ih₂ =>
      obtain ⟨h₁, h₂, hA, hB, hRho, hRho', hSigma⟩ := hOriginal
      obtain ⟨hWF₁, hWF₂, hVia⟩ := hWF
      refine ⟨ih₁ h₁ hWF₁, ih₂ h₂ hWF₂, ?_⟩
      let hNode :
          AllOriginal (hNoEq := by first | exact hNoEq | done)
            (.resolve T₁ T₂ resolvedA resolvedB rho rho' sigma) :=
        ⟨h₁, h₂, hA, hB, hRho, hRho', hSigma⟩
      have hLowerVia :=
        FreshGroundLanguage.IsResolventVia.lower (hNoEq := by first | exact hNoEq | done) hVia
          (AllOriginal.label (hNoEq := by first | exact hNoEq | done) hNode)
          (AllOriginal.label (hNoEq := by first | exact hNoEq | done) h₁)
          (AllOriginal.label (hNoEq := by first | exact hNoEq | done) h₂)
          hA hB hRho hRho' hSigma
      rw [← lower_label (hNoEq := by first | exact hNoEq | done)
          (.resolve T₁ T₂ resolvedA resolvedB rho rho' sigma) hNode,
        ← lower_label (hNoEq := by first | exact hNoEq | done) T₁ h₁, ← lower_label (hNoEq := by first | exact hNoEq | done) T₂ h₂] at hLowerVia
      change
        IsResolventVia (hNoEq := by first | exact hNoEq | done)
          (label (hNoEq := by first | exact hNoEq | done)
            (lower (hNoEq := by first | exact hNoEq | done)
              (.resolve T₁ T₂ resolvedA resolvedB rho rho' sigma)
              hNode))
          (label (hNoEq := by first | exact hNoEq | done) (lower (hNoEq := by first | exact hNoEq | done) T₁ h₁))
          (label (hNoEq := by first | exact hNoEq | done) (lower (hNoEq := by first | exact hNoEq | done) T₂ h₂))
          (lowerClause (hNoEq := by first | exact hNoEq | done) resolvedA hA)
          (lowerClause (hNoEq := by first | exact hNoEq | done) resolvedB hB)
          (lowerSubst rho hRho)
          (lowerSubst rho' hRho')
          (lowerSubst sigma hSigma)
      exact hLowerVia

-- retained: used by LCS.FOResolution.Method.Completeness.Completeness
/-- Leaf provenance through the clause embedding descends with the tree. -/
theorem lower_leavesFrom {L : Language} (hNoEq : L.withoutEquality)
    {S : FOClause L hNoEq → Prop}
    {T : FOResolutionTree (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq)}
    (hOriginal : AllOriginal (hNoEq := by first | exact hNoEq | done) T)
    (hLeaves :
      leavesFrom (hNoEq := by first | exact hNoEq | done) T (fun C => ∃ D, S D ∧ C = liftClause (hNoEq := by first | exact hNoEq | done) D)) :
    leavesFrom (hNoEq := by first | exact hNoEq | done) (lower (hNoEq := by first | exact hNoEq | done) T hOriginal) S := by
  induction T with
  | axiom_ C =>
      obtain ⟨D, hD, hLift⟩ := hLeaves
      have hLower : lowerClause (hNoEq := by first | exact hNoEq | done) C hOriginal = D := by
        apply liftClause_injective (hNoEq := by first | exact hNoEq | done)
        exact (liftClause_lowerClause (hNoEq := by first | exact hNoEq | done) hOriginal).trans hLift
      change S (lowerClause (hNoEq := by first | exact hNoEq | done) C hOriginal)
      rw [hLower]
      exact hD
  | resolve T₁ T₂ resolvedA resolvedB rho rho' sigma ih₁ ih₂ =>
      obtain ⟨h₁, h₂, _, _, _, _, _⟩ := hOriginal
      exact ⟨ih₁ h₁ hLeaves.1, ih₂ h₂ hLeaves.2⟩



end FOResolutionTree
end LCS.FOResolution.Method
end

section
namespace LCS.FOResolution.Method
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Unification

/-- Example 8.5.1: Clause A = {neg P(z, a), neg P(z, x), neg P(x, z)}
    with z = var 0, x = var 4. -/
@[blueprint "chap8__example_8_5_1" (main := true)]
def exResClause_A : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.neg (exPred_P (Term.var 0) exSkolemConst_a),
    FOLiteralCore.neg (exPred_P (Term.var 0) (Term.var 4)),
    FOLiteralCore.neg (exPred_P (Term.var 4) (Term.var 0)) ]

/-- Example 8.5.1: Clause B = {P(z, f(z)), P(z, a)} with z = var 0. -/
@[blueprint "chap8__example_8_5_1" (main := true)]
def exResClause_B : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.pos (exPred_P (Term.var 0) (exSkolemFunc_f 0)),
    FOLiteralCore.pos (exPred_P (Term.var 0) exSkolemConst_a) ]

/-- Example 8.5.1 (companion): A' = {neg P(z, a), neg P(z, x)}, the
    subset of A for the first resolvent computation. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_A'_first : List (FOLiteral exClauseFormLang rfl) :=
  [ FOLiteralCore.neg (exPred_P (Term.var 0) exSkolemConst_a),
    FOLiteralCore.neg (exPred_P (Term.var 0) (Term.var 4)) ]

/-- Example 8.5.1 (companion): B' = {P(z, a)}, the subset of B for the
    first resolvent computation. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_B'_first : List (FOLiteral exClauseFormLang rfl) :=
  [ FOLiteralCore.pos (exPred_P (Term.var 0) exSkolemConst_a) ]

/-- Example 8.5.1 (companion): rho = (z_1/z), renaming z (var 0) to z_1
    (var 1). All other variables map to themselves. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_rho_first : Nat → Term exClauseFormLang
  | 0 => Term.var 1  -- z -> z_1
  | n => Term.var n

/-- Example 8.5.1 (companion): rho' = (z_2/z), renaming z (var 0) to
    z_2 (var 2). All other variables map to themselves. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_rho'_first : Nat → Term exClauseFormLang
  | 0 => Term.var 2  -- z -> z_2
  | n => Term.var n

/-- Example 8.5.1 (companion): sigma = (z_1/z_2, a/x), the MGU for the
    first resolvent. Maps z_2 (var 2) to z_1 (var 1), x (var 4) to a. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_sigma_first : Nat → Term exClauseFormLang
  | 2 => Term.var 1        -- z_2 -> z_1
  | 4 => exSkolemConst_a   -- x -> a
  | n => Term.var n

/-- Example 8.5.1: C = {neg P(a, z_1), P(z_1, f(z_1))}, the first
    resolvent of A and B. -/
@[blueprint "chap8__example_8_5_1" (main := true)]
def exRes_C_first : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.neg (exPred_P exSkolemConst_a (Term.var 1)),
    FOLiteralCore.pos (exPred_P (Term.var 1) (exSkolemFunc_f 1)) ]

/-- Example 8.5.1 (companion): A' = A = {neg P(z, a), neg P(z, x),
    neg P(x, z)}, the full clause A selected for the second resolvent
    computation. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_A'_second : List (FOLiteral exClauseFormLang rfl) :=
  exResClause_A

/-- Example 8.5.1 (companion): B' = {P(z, a)}, the subset of B for the
    second resolvent computation (same as the first computation). -/
@[blueprint "chap8__example_8_5_1"]
def exRes_B'_second : List (FOLiteral exClauseFormLang rfl) :=
  [ FOLiteralCore.pos (exPred_P (Term.var 0) exSkolemConst_a) ]

/-- Example 8.5.1 (companion): rho for the second resolvent, same as
    first: (z_1/z), renaming z (var 0) to z_1 (var 1). -/
@[blueprint "chap8__example_8_5_1"]
def exRes_rho_second : Nat → Term exClauseFormLang
  | 0 => Term.var 1
  | n => Term.var n

/-- Example 8.5.1 (companion): rho' for the second resolvent, same as
    first: (z_2/z), renaming z (var 0) to z_2 (var 2). -/
@[blueprint "chap8__example_8_5_1"]
def exRes_rho'_second : Nat → Term exClauseFormLang
  | 0 => Term.var 2
  | n => Term.var n

/-- Example 8.5.1 (companion): sigma = (a/z_1, a/z_2, a/x), the MGU for
    the second resolvent computation. -/
@[blueprint "chap8__example_8_5_1"]
def exRes_sigma_second : Nat → Term exClauseFormLang
  | 1 => exSkolemConst_a   -- z_1 -> a
  | 2 => exSkolemConst_a   -- z_2 -> a
  | 4 => exSkolemConst_a   -- x -> a
  | n => Term.var n

/-- Example 8.5.1: C = {P(a, f(a))}, the second resolvent of A and B
    obtained by taking A' = A. -/
@[blueprint "chap8__example_8_5_1" (main := true)]
def exRes_C_second : FOClause exClauseFormLang rfl :=
  [ FOLiteralCore.pos (exPred_P exSkolemConst_a
      (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a))) ]

/-- Example 8.5.1: The worked example demonstrating two distinct
    resolvents of A and B with different literal subsets and MGUs. -/
@[blueprint "chap8__example_8_5_1" (main := true)]
def exResolventExample : FOClause exClauseFormLang rfl × FOClause exClauseFormLang rfl :=
  (exRes_C_first, exRes_C_second)

-- ===================================================================
-- Example 8.5.2: Resolution refutation example
-- ===================================================================

/-- Example 8.5.2: C_1 = {neg P(z_1, a), neg P(z_1, x), neg P(x, z_1)}
    with z_1 = var 1, x = var 4. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefClause_C1 : FOClause exClauseFormLang rfl :=
  exClause_C1

/-- Example 8.5.2: C_2 = {P(z_2, f(z_2)), P(z_2, a)} with z_2 = var 2. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefClause_C2 : FOClause exClauseFormLang rfl :=
  exClause_C2

/-- Example 8.5.2: C_3 = {P(f(z_3), z_3), P(z_3, a)} with z_3 = var 3. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefClause_C3 : FOClause exClauseFormLang rfl :=
  exClause_C3

/-- Example 8.5.2: Step 1 -- C_2 resolves with C_1 using identity
    separating pair and mgu (a/z_1, a/z_2, a/x), yielding {P(a, f(a))}. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefStep1 : FOResolutionTree exClauseFormLang rfl :=
  .resolve
    (.axiom_ exRefClause_C2)
    (.axiom_ exRefClause_C1)
    -- resolvedA: P(z_2, a) from C_2
    [ FOLiteralCore.pos (exPred_P (Term.var 2) exSkolemConst_a) ]
    -- resolvedB: all of C_1
    exRefClause_C1
    (fun n => Term.var n)  -- rho = identity
    (fun n => Term.var n)  -- rho' = identity
    (fun n => match n with -- sigma = (a/z_1, a/z_2, a/x)
      | 1 => exSkolemConst_a
      | 2 => exSkolemConst_a
      | 4 => exSkolemConst_a
      | n => Term.var n)

/-- Example 8.5.2: Step 2 -- C_1 resolves with C_3 using identity
    separating pair and mgu (a/z_1, a/x, a/z_3), yielding {P(f(a), a)}. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefStep2 : FOResolutionTree exClauseFormLang rfl :=
  .resolve
    (.axiom_ exRefClause_C1)
    (.axiom_ exRefClause_C3)
    -- resolvedA: all of C_1 (negative literals)
    exRefClause_C1
    -- resolvedB: P(z_3, a) from C_3
    [ FOLiteralCore.pos (exPred_P (Term.var 3) exSkolemConst_a) ]
    (fun n => Term.var n)
    (fun n => Term.var n)
    (fun n => match n with
      | 1 => exSkolemConst_a
      | 3 => exSkolemConst_a
      | 4 => exSkolemConst_a
      | n => Term.var n)

/-- Example 8.5.2: Step 3 -- C_1 resolves with V = {P(f(a), a)}
    from step 2, using mgu (f(a)/z_1, a/x), yielding {neg P(a, f(a))}. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefStep3 : FOResolutionTree exClauseFormLang rfl :=
  .resolve
    (.axiom_ exRefClause_C1)
    exRefStep2
    -- The first two negative literals of C_1.
    [ FOLiteralCore.neg (exPred_P (Term.var 1) exSkolemConst_a),
      FOLiteralCore.neg (exPred_P (Term.var 1) (Term.var 4)) ]
    -- All of V = {P(f(a), a)}.
    [ FOLiteralCore.pos (exPred_P
        (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)) exSkolemConst_a) ]
    (fun n => Term.var n)
    (fun n => Term.var n)
    (fun n => match n with
      | 1 => Term.func ExClauseFunc.f (fun _ => exSkolemConst_a)
      | 4 => exSkolemConst_a
      | n => Term.var n)

/-- Example 8.5.2: Step 4 -- U resolves with W, the result of the
    C_1,V inference, using the identity mgu and yielding the empty clause. -/
@[blueprint "chap8__example_8_5_2" (main := true)]
def exRefStep4 : FOResolutionTree exClauseFormLang rfl :=
  .resolve
    exRefStep1
    exRefStep3
    -- resolvedA: all of step 1 label = {P(a,f(a))}
    [ FOLiteralCore.pos (exPred_P exSkolemConst_a
        (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a))) ]
    -- resolvedB: all of step 3 label = {neg P(a,f(a))}
    [ FOLiteralCore.neg (exPred_P exSkolemConst_a
        (Term.func ExClauseFunc.f (fun _ => exSkolemConst_a))) ]
    (fun n => Term.var n)
    (fun n => Term.var n)
    (fun n => Term.var n)  -- identity mgu


end LCS.FOResolution.Method
end

