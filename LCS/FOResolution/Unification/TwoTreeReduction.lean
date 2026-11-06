import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.FreeGeneration
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FOResolution.Unification.Substitutions
import LCS.FOResolution.Unification.Unifiers
import Attach
import LCS.FOResolution.Unification.TwoTreeReduction.ProofsStamp

section
namespace LCS.FOResolution.Unification
open LCS.FirstOrder.Basic
open LCS.FirstOrder.Syntax.FreeGeneration
open LCS.FirstOrder.SyntaxN.Variables

-- ===================================================================
-- Lemma 8.4.1: Reduction of multi-tree unification to pairwise
-- ===================================================================

/-- Lemma 8.4.1: A substitution sigma unifies {t_1, ..., t_m} iff sigma
    unifies the pair {#(t_1,...,t_m), #(t_1,...,t_1)} for a fresh #. -/
@[blueprint "chap8__lemma_8_4_1" (main := true)]
theorem unifier_iff_auxiliary_unifier {L : Language}
    (ts : List (Term L)) (sigma : Nat → Term L)
    (L' : Language)
    (embed : L.funSymbols → L'.funSymbols)
    (sharp : L'.funSymbols)
    (h_arity_embed : ∀ f, L'.funArity (embed f) = L.funArity f)
    (h_arity_sharp : L'.funArity sharp = ts.length)
    (liftTerm : Term L → Term L')
    (h_lift_var : ∀ x, liftTerm (Term.var x) = Term.var x)
    (h_lift_const : ∀ c, liftTerm (Term.const c) =
      liftTerm (Term.const c))
    (h_lift_func : ∀ (f : L.funSymbols) (args : Fin (L.funArity f) → Term L),
      liftTerm (Term.func f args) =
        Term.func (embed f)
          (fun i => liftTerm (args (i.cast (h_arity_embed f)))))
    (h_lift_subst : ∀ t, liftTerm (termSubstAll t sigma) =
      termSubstAll (liftTerm t) (fun x => liftTerm (sigma x)))
    (h_lift_injective : ∀ a b, liftTerm a = liftTerm b → a = b) :
    IsUnifierCore sigma ts ↔
      IsUnifierCore (fun x => liftTerm (sigma x))
        [Term.func sharp (fun i =>
          liftTerm (ts.get (i.cast h_arity_sharp))),
         Term.func sharp (fun _ =>
          match ts with
          | [] => Term.var 0
          | t :: _ => liftTerm t)] 

end LCS.FOResolution.Unification
end
