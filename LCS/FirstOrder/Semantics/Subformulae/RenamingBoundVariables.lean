import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.Substitution
import LCS.FirstOrder.Syntax.Variables
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.Semantics.Substitution
import LCS.Propositional.Syntax
import LCS.Propositional.Semantics
import Attach
import LCS.FirstOrder.Semantics.Subformulae.RenamingBoundVariables.ProofsStamp

section
namespace LCS.FirstOrder.Semantics.Subformulae
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax
open LCS.FirstOrder.Syntax.Substitution
open LCS.FirstOrder.Syntax.Variables
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.FirstOrder.SemanticsN
open LCS.FirstOrder.Semantics
open LCS.FirstOrder.Semantics.Substitution (coincidenceLemma)
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics

-- ===================================================================
-- Helper: Term coincidence lemma (local)
-- ===================================================================

-- termCoincidence and coincidenceLemmaN imported from SemanticsN

-- ===================================================================
-- Helper: Variable substitution evaluation with isFreeForN
-- ===================================================================

-- retained: used by LCS.FirstOrder.Semantics.Subformulae.Part2
theorem termVarSubstEval {L : Language} (M : Structure L)
    (s : Assignment M) (t : Term L) (i j : Nat) :
    termEval M s (termSubst t (Term.var j) i) =
    termEval M (assignUpdate s i (s j)) t := by
-- BEGIN PROOF
  induction t with
  | var x =>
    unfold termSubst termEval
    by_cases hxi : x = i
    · subst hxi; simp [assignUpdate]
    · simp [assignUpdate, hxi]
  | const c => simp [termSubst, termEval]
  | func f ts ih =>
    simp only [termSubst, termEval]
    congr 1; funext k; exact ih k

-- ===================================================================
-- Lemma 5.3.4: Alpha-equivalence and rectification
-- ===================================================================

/-- Lemma 5.3.4(i), universal: Renaming bound variable i to j
preserves the formula's meaning when j is free for i in A and
j does not occur free in A except possibly as i. -/
@[blueprint "chap5__lemma_5_3_4" (main := true)]
theorem alphaEquivUnivF {L : Language} (A : Formula L) (i j : Nat)
    (hFree : isFreeFor (Term.var j) i A)
    (hFresh : ¬ (j ∈ (formulaFV A \ Set.singleton i))) :
    universallyValid
      (Formula.equiv_ (Formula.all i A)
        (Formula.all j (formulaSubst A (Term.var j) i))) 

/-- Lemma 5.3.4(i), existential: Renaming bound variable i to j
preserves the formula's meaning when j is free for i in A and
j does not occur free in A except possibly as i. -/
@[blueprint "chap5__lemma_5_3_4" (main := true)]
theorem alphaEquivExF {L : Language} (A : Formula L) (i j : Nat)
    (hFree : isFreeFor (Term.var j) i A)
    (hFresh : ¬ (j ∈ (formulaFV A \ Set.singleton i))) :
    universallyValid
      (Formula.equiv_ (Formula.ex i A)
        (Formula.ex j (formulaSubst A (Term.var j) i))) 

end LCS.FirstOrder.Semantics.Subformulae
end
