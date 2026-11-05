import LCS.FirstOrder.SyntaxN

/-! Computable equality for terms and normalized formulas from decidable symbol
equality. Callers install these definitions locally with `letI` or `haveI`. -/

namespace LCS.FirstOrder.Basic

/-- Decide term equality by structural recursion and finite argument comparison.
This computable decision procedure can be installed as a local instance. -/
def Term.decEqOfSymbols {L : Language} [DecidableEq L.funSymbols]
    [DecidableEq L.constSymbols] : DecidableEq (Term L) := fun a b => by
  cases a with
  | var x =>
    cases b <;> try (apply isFalse; intro h; cases h; done)
    rename_i y
    exact decidable_of_iff (x = y) (by simp)
  | const c =>
    cases b <;> try (apply isFalse; intro h; cases h; done)
    rename_i d
    exact decidable_of_iff (c = d) (by simp)
  | func f ts =>
    cases b <;> try (apply isFalse; intro h; cases h; done)
    rename_i g ss
    if h : f = g then
      subst g
      letI : DecidablePred (fun i => ts i = ss i) :=
        fun i => Term.decEqOfSymbols (ts i) (ss i)
      exact decidable_of_iff (∀ i, ts i = ss i) (by
        simp only [Term.func.injEq, true_and, heq_eq_eq]
        exact funext_iff.symm)
    else
      exact isFalse (by intro e; exact h ((Term.func.injEq ..).mp e).1)
termination_by structural a _ => a

end LCS.FirstOrder.Basic

namespace LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.Basic

/-- Decide normalized formula equality by structural recursion, using computable
term equality at atoms. Equality-availability proofs are proof irrelevant.
Callers install this decision procedure locally; it is not a global instance. -/
def FormulaN.decEqOfSymbols {L : Language} [DecidableEq L.predSymbols]
    [DecidableEq L.funSymbols] [DecidableEq L.constSymbols] :
    DecidableEq (FormulaN L) := fun a b => by
  letI : DecidableEq (Term L) := Term.decEqOfSymbols
  cases a with
  | predN P ts =>
    cases b <;> try (apply isFalse; intro h; cases h; done)
    rename_i Q ss
    if h : P = Q then
      subst Q
      exact decidable_of_iff (∀ i, ts i = ss i) (by
        simp only [FormulaN.predN.injEq, true_and, heq_eq_eq]
        exact funext_iff.symm)
    else
      exact isFalse (by intro e; exact h ((FormulaN.predN.injEq ..).mp e).1)
  | eq_ h s t =>
    cases b <;> try (apply isFalse; intro e; cases e; done)
    rename_i h' u v
    exact decidable_of_iff (s = u ∧ t = v) (by simp)
  | neg A =>
    cases b <;> try (apply isFalse; intro h; cases h; done)
    rename_i B
    letI : Decidable (A = B) := FormulaN.decEqOfSymbols A B
    exact decidable_of_iff (A = B) (by simp)
  | conj A B =>
    cases b <;> try (apply isFalse; intro h; cases h; done)
    rename_i C D
    letI : Decidable (A = C) := FormulaN.decEqOfSymbols A C
    letI : Decidable (B = D) := FormulaN.decEqOfSymbols B D
    exact decidable_of_iff (A = C ∧ B = D) (by simp)
  | disj A B =>
    cases b <;> try (apply isFalse; intro h; cases h; done)
    rename_i C D
    letI : Decidable (A = C) := FormulaN.decEqOfSymbols A C
    letI : Decidable (B = D) := FormulaN.decEqOfSymbols B D
    exact decidable_of_iff (A = C ∧ B = D) (by simp)
  | impl A B =>
    cases b <;> try (apply isFalse; intro h; cases h; done)
    rename_i C D
    letI : Decidable (A = C) := FormulaN.decEqOfSymbols A C
    letI : Decidable (B = D) := FormulaN.decEqOfSymbols B D
    exact decidable_of_iff (A = C ∧ B = D) (by simp)
  | all x A =>
    cases b <;> try (apply isFalse; intro h; cases h; done)
    rename_i y B
    letI : Decidable (A = B) := FormulaN.decEqOfSymbols A B
    exact decidable_of_iff (x = y ∧ A = B) (by simp)
  | ex x A =>
    cases b <;> try (apply isFalse; intro h; cases h; done)
    rename_i y B
    letI : Decidable (A = B) := FormulaN.decEqOfSymbols A B
    exact decidable_of_iff (x = y ∧ A = B) (by simp)
termination_by structural a _ => a

private abbrev equalityExampleLanguage : Language where
  funSymbols := Nat
  funArity := id
  constSymbols := Nat
  predSymbols := Nat
  predArity := id
  hasEquality := true

private def equalityExampleFormula (n : Nat) : FormulaN equalityExampleLanguage :=
  .all 0 (.ex 1 (.impl
    (.conj (.predN 2 (fun i => .func 2 (fun j =>
      if i.val = j.val then .const n else .var j.val))) (.eq_ rfl (.var 0) (.const 1)))
    (.disj (.neg (.predN 0 Fin.elim0)) (.eq_ rfl (.const 0) (.const 0)))))

example :
    (letI : DecidableEq (FormulaN equalityExampleLanguage) := FormulaN.decEqOfSymbols
     decide (equalityExampleFormula 0 = equalityExampleFormula 0)) = true := rfl

example :
    (letI : DecidableEq (FormulaN equalityExampleLanguage) := FormulaN.decEqOfSymbols
     decide (equalityExampleFormula 0 = equalityExampleFormula 1)) = false := rfl

example :
    (letI : DecidableEq (FormulaN equalityExampleLanguage) := FormulaN.decEqOfSymbols
     decide (FormulaN.predN (L := equalityExampleLanguage) 0 Fin.elim0 =
       FormulaN.predN (L := equalityExampleLanguage) 1 (fun _ => Term.var 0))) = false := rfl

example :
    (letI : DecidableEq (Term equalityExampleLanguage) := Term.decEqOfSymbols
     decide (Term.func (L := equalityExampleLanguage) 0 Fin.elim0 =
       Term.func (L := equalityExampleLanguage) 1 (fun _ => Term.const 0))) = false := rfl

end LCS.FirstOrder.SyntaxN
