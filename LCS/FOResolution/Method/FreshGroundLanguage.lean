import LCS.Item
import LCS.Util
import LCS.FOResolution.ClauseForm
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.SeparatingPairs
import LCS.FOResolution.Method.Resolvents
import Attach
import LCS.FOResolution.Method.FreshGroundLanguage.ProofsStamp

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
/-- Structural predicate that every term of an atom uses original symbols. -/
def IsOriginalAtom {L : Language} (hNoEq : L.withoutEquality) :
    FOAtom (FreshGroundLanguage L) ((FreshGroundLanguage.withoutEquality_iff L).2 hNoEq) → Prop
  | .predN _ args => ∀ i, IsOriginalTerm (args i)
  | .eq_ _ lhs rhs => IsOriginalTerm lhs ∧ IsOriginalTerm rhs

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

-- retained: used by LCS.FOResolution.Method.GroundExtension
/-- Clause lifting distributes over append. -/
theorem liftClause_append {L : Language} (hNoEq : L.withoutEquality)
    (left right : FOClause L hNoEq) :
    liftClause (hNoEq := by first | exact hNoEq | done) (left ++ right) = liftClause (hNoEq := by first | exact hNoEq | done) left ++ liftClause (hNoEq := by first | exact hNoEq | done) right :=
  List.map_append

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

end FreshGroundLanguage
end LCS.FOResolution.Method
end
