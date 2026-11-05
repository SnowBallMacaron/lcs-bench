import LCS.FirstOrder.Syntax.Algebra

namespace LCS.FirstOrder.Basic.Language

open LCS.FirstOrder.Syntax.Algebra

open LCS.FirstOrder.ManySorted.CongruenceClosure

helper /-- Definition 5.2.1 (companion): Variables have result sort term. -/
theorem Basic.Language.twoSortedAlphabet_var_resultSort (L : _root_.LCS.FirstOrder.Basic.Language) (x : Nat) :
    (twoSortedAlphabet L).resultSort (.var x) = FirstOrderSort.term := rfl

helper /-- Definition 5.2.1 (companion): Constants have result sort term. -/
theorem Basic.Language.twoSortedAlphabet_const_resultSort (L : _root_.LCS.FirstOrder.Basic.Language) (c : L.constSymbols) :
    (twoSortedAlphabet L).resultSort (.const c) = FirstOrderSort.term := rfl

helper /-- Definition 5.2.1 (companion): Function symbols have result sort term. -/
theorem Basic.Language.twoSortedAlphabet_func_resultSort (L : _root_.LCS.FirstOrder.Basic.Language) (f : L.funSymbols) :
    (twoSortedAlphabet L).resultSort (.func f) = FirstOrderSort.term := rfl

helper /-- Definition 5.2.1 (companion): Predicate symbols have result sort formula. -/
theorem Basic.Language.twoSortedAlphabet_pred_resultSort (L : _root_.LCS.FirstOrder.Basic.Language) (P : L.predSymbols) :
    (twoSortedAlphabet L).resultSort (.pred P) = FirstOrderSort.formula := rfl

helper /-- Definition 5.2.1 (companion): Bottom has result sort formula. -/
theorem Basic.Language.twoSortedAlphabet_bot_resultSort (L : _root_.LCS.FirstOrder.Basic.Language) :
    (twoSortedAlphabet L).resultSort .bot = FirstOrderSort.formula := rfl

end LCS.FirstOrder.Basic.Language

namespace LCS.FirstOrder.Syntax.Algebra

open LCS.FirstOrder.Basic

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.FirstOrder.Syntax.FreeGeneration

helper /-- Theorem 5.2.2 (companion): The operation A_i on strings prints ∀x_i A. -/
theorem Syntax.Algebra.stringAlgebra_all {L : Language} (i : Nat) (A : _root_.LCS.FirstOrder.Syntax.Formula L) :
    syntaxApply (stringAlgebra L) (.all i) (fun _ => printTree .formula A) =
      printTree .formula (.all i A) := by
  change printTree .formula (Formula.all i (parseString .formula (printTree .formula A))) = _
  rw [parse_print]

helper /-- Theorem 5.2.2 (companion): The operation E_i on strings prints ∃x_i A. -/
theorem Syntax.Algebra.stringAlgebra_ex {L : Language} (i : Nat) (A : _root_.LCS.FirstOrder.Syntax.Formula L) :
    syntaxApply (stringAlgebra L) (.ex i) (fun _ => printTree .formula A) =
      printTree .formula (.ex i A) := by
  change printTree .formula (Formula.ex i (parseString .formula (printTree .formula A))) = _
  rw [parse_print]

helper /-- Theorem 5.2.2 (proof helper): composition of two-sorted homomorphisms. -/
def Syntax.Algebra.homComp {S : MSRankedAlphabet} {A B C : MSAlgebra S}
    (g : MSHom B C) (h : MSHom A B) : MSHom A C :=
  { map := fun s x => g.map s (h.map s x)
    preserves := by
      intro op args
      rw [h.preserves, g.preserves] }

helper /-- Theorem 5.2.2 (proof helper): the homomorphism from the string algebra induced by
folding the parsed tree. -/
noncomputable def Syntax.Algebra.stringFoldHom {L : Language} (A : MSAlgebra (syntaxAlphabet L))
    (ρ : Nat → A.carrier .term) : MSHom (stringAlgebra L) A :=
  { map := fun s x => (foldHom A ρ).map s (parseString s x)
    preserves := by
      intro op args
      change (foldHom A ρ).map _ (parseString _ (printTree _ _)) = _
      rw [parse_print]
      exact (foldHom A ρ).preserves op _ }

proof_of stringAlgebra_free := by
  -- BEGIN PROOF
  intro A ρ
  refine ⟨Syntax.Algebra.stringFoldHom A ρ, ?_, ?_⟩
  · intro i
    change foldTerm A ρ (parseString .term (printTree .term (.var i))) = _
    rw [parse_print]
    rfl
  · intro g hg
    have hu := fold_unique A ρ (Syntax.Algebra.homComp g (treeStringIso L).toMSHom) hg
    apply hom_ext
    funext s x
    have hx := congrFun (congrFun (congrArg MSHom.map hu) s) (parseString s x)
    change g.map s (printTree s (parseString s x)) = (foldHom A ρ).map s (parseString s x) at hx
    rw [print_parse] at hx
    exact hx

end LCS.FirstOrder.Syntax.Algebra

namespace LCS.FirstOrder.Syntax.Algebra

open LCS.FirstOrder.Basic

open LCS.FirstOrder.ManySorted.CongruenceClosure

helper /-- Definition 5.3.1 (companion): The term carrier is exactly M. -/
theorem Syntax.Algebra.structureAlgebra_term {L : Language} (M : Structure L) :
    (structureAlgebra M).carrier .term = M.carrier := rfl

helper /-- Definition 5.3.1 (companion): The formula carrier is the truth-value type Prop. -/
theorem Syntax.Algebra.structureAlgebra_formula {L : Language} (M : Structure L) :
    (structureAlgebra M).carrier .formula = Prop := rfl

helper /-- Definition 5.3.1 (companion): Constant interpretations are unchanged. -/
theorem Syntax.Algebra.structureAlgebra_const {L : Language} (M : Structure L) (c : L.constSymbols) :
    (structureAlgebra M).operation (.const c) (fun i => Fin.elim0 i) = M.interpConst c := rfl

end LCS.FirstOrder.Syntax.Algebra
