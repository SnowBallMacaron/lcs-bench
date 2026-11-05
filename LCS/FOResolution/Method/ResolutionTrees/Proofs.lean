import LCS.FOResolution.Method.ResolutionTrees

section

namespace LCS.FOResolution.Method

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification













end LCS.FOResolution.Method

end

section

namespace LCS.FOResolution.Method

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FOResolution.ClauseForm

open LCS.FOResolution.Unification

namespace FreshGroundLanguage

proof_of withoutEquality_iff := Iff.rfl

helper /-- Every symbol in the new summand is the distinguished fresh constant. -/
theorem Method.FreshGroundLanguage.freshConstantSymbol_unique {L : Language} (u : Unit) :
    (Sum.inr u : L.constSymbols ⊕ Unit) = freshConstantSymbol := by
  cases u
  rfl

helper /-- The extension preserves the type of function symbols definitionally. -/
theorem Method.FreshGroundLanguage.funSymbols_eq (L : Language) :
    (FreshGroundLanguage L).funSymbols = L.funSymbols :=
  rfl

helper /-- The extension preserves function arities definitionally. -/
theorem Method.FreshGroundLanguage.funArity_eq (L : Language) :
    (FreshGroundLanguage L).funArity = L.funArity :=
  rfl

helper /-- The extension preserves the type of predicate symbols definitionally. -/
theorem Method.FreshGroundLanguage.predSymbols_eq (L : Language) :
    (FreshGroundLanguage L).predSymbols = L.predSymbols :=
  rfl

helper /-- The extension preserves predicate arities definitionally. -/
theorem Method.FreshGroundLanguage.predArity_eq (L : Language) :
    (FreshGroundLanguage L).predArity = L.predArity :=
  rfl

helper /-- The extension preserves the equality flag definitionally. -/
theorem Method.FreshGroundLanguage.hasEquality_eq (L : Language) :
    (FreshGroundLanguage L).hasEquality = L.hasEquality :=
  rfl









helper /-- The fresh seed cannot be confused with any lifted base-language term. -/
theorem Method.FreshGroundLanguage.seed_ne_liftTerm {L : Language} (t : Term L) :
    (@seed L) ≠ liftTerm t := by
  intro h
  cases t with
  | var => cases h
  | const c =>
      exact Sum.inr_ne_inl (@Term.const.inj (FreshGroundLanguage L)
        freshConstantSymbol (Sum.inl c) h)
  | func => cases h



helper /-- Certified atom descent is a left inverse of the atom lift. -/
theorem Method.FreshGroundLanguage.lowerAtom_liftAtom {L : Language} (hNoEq : L.withoutEquality) (atom : FOAtom L hNoEq) :
    lowerAtom (hNoEq := by first | exact hNoEq | done) (liftAtom (hNoEq := by first | exact hNoEq | done) atom) (liftAtom_isOriginal (hNoEq := by first | exact hNoEq | done) atom) = atom := by
  cases atom with
  | predN P args =>
      simp only [liftAtom, lowerAtom]
      congr 1
      funext i
      exact lowerTerm_liftTerm (args i)
  | eq_ hL lhs rhs =>
      simp only [liftAtom, lowerAtom]
      congr 1
      · exact lowerTerm_liftTerm lhs
      · exact lowerTerm_liftTerm rhs





helper /-- Certified literal descent is a left inverse of the literal lift. -/
theorem Method.FreshGroundLanguage.lowerLiteral_liftLiteral {L : Language} (hNoEq : L.withoutEquality) (lit : FOLiteral L hNoEq) :
    lowerLiteral (hNoEq := by first | exact hNoEq | done) (liftLiteral (hNoEq := by first | exact hNoEq | done) lit) (liftLiteral_isOriginal (hNoEq := by first | exact hNoEq | done) lit) = lit := by
  cases lit with
  | pos atom =>
      exact congrArg FOLiteralCore.pos (lowerAtom_liftAtom (hNoEq := by first | exact hNoEq | done) atom)
  | neg atom =>
      exact congrArg FOLiteralCore.neg (lowerAtom_liftAtom (hNoEq := by first | exact hNoEq | done) atom)





helper /-- Lifted original clauses lower exactly to their source clauses. -/
theorem Method.FreshGroundLanguage.lowerClause_liftClause {L : Language} (hNoEq : L.withoutEquality) (C : FOClause L hNoEq) :
    lowerClause (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) C) (liftClause_isOriginal (hNoEq := by first | exact hNoEq | done) C) = C := by
  induction C with
  | nil =>
      rfl
  | cons lit rest ih =>
      change
        lowerLiteral (hNoEq := by first | exact hNoEq | done) (liftLiteral (hNoEq := by first | exact hNoEq | done) lit) (liftLiteral_isOriginal (hNoEq := by first | exact hNoEq | done) lit) ::
            lowerClause (hNoEq := by first | exact hNoEq | done) (liftClause (hNoEq := by first | exact hNoEq | done) rest) (liftClause_isOriginal (hNoEq := by first | exact hNoEq | done) rest) =
          lit :: rest
      rw [lowerLiteral_liftLiteral (hNoEq := by first | exact hNoEq | done) lit, ih]



helper /-- Every lifted substitution is original-symbol-valued. -/
theorem Method.FreshGroundLanguage.liftSubst_isOriginal {L : Language} (sigma : Nat → Term L) :
    IsOriginalSubst (liftSubst sigma) :=
  fun x => liftTerm_isOriginal (sigma x)

helper /-- Certified substitution descent is a left inverse of lifting. -/
theorem Method.FreshGroundLanguage.lowerSubst_liftSubst {L : Language} (sigma : Nat → Term L) :
    lowerSubst (liftSubst sigma) (liftSubst_isOriginal sigma) = sigma := by
  funext x
  exact lowerTerm_liftTerm (sigma x)







end FreshGroundLanguage

end LCS.FOResolution.Method

end
