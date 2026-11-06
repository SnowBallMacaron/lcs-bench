import LCS.Propositional.Infinite.KonigLemma

section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

proof_of konig_lemma := by
  -- BEGIN PROOF
    -- First, show root has infinite descendants
    have hroot_inf : ¬ Set.Finite (T.descendants T.root) := by
      intro hfin
      apply h_infinite
      apply Set.Finite.subset hfin
      intro n hn
      exact ⟨hn, h_allReachable n hn⟩
    -- Build a choice function: given a node with infinite descendants,
    -- pick a child with infinite descendants
    have choose_child : ∀ p, T.isNode p → ¬ Set.Finite (T.descendants p) →
        ∃ c, T.children p c ∧ ¬ Set.Finite (T.descendants c) := by
      intro p hp hinf
      exact T.exists_child_infinite_desc p hp hinf (fun n hn => h_tree p n hn.1 hn.2)
    -- Use Classical.choose to make a definite selection function
    let chosenChild : (p : T.Node) → T.isNode p → ¬ Set.Finite (T.descendants p) → T.Node :=
      fun p hp hinf => Classical.choose (choose_child p hp hinf)
    have chosenChild_spec : ∀ p hp hinf,
        T.children p (chosenChild p hp hinf) ∧
        ¬ Set.Finite (T.descendants (chosenChild p hp hinf)) :=
      fun p hp hinf => Classical.choose_spec (choose_child p hp hinf)
    have chosenChild_isNode : ∀ p hp hinf,
        T.isNode (chosenChild p hp hinf) :=
      fun p hp hinf =>
        T.childrenAreNodes p _ hp (chosenChild_spec p hp hinf).1
    -- Bundle type for the recursion
    -- Use Nat.rec to iterate: seq n = (node_n, isNode_n, infDesc_n)
    let stepB : { p : T.Node // T.isNode p ∧ ¬ Set.Finite (T.descendants p) } →
                { p : T.Node // T.isNode p ∧ ¬ Set.Finite (T.descendants p) } :=
      fun ⟨p, hp, hinf⟩ =>
        ⟨chosenChild p hp hinf, chosenChild_isNode p hp hinf, (chosenChild_spec p hp hinf).2⟩
    let init : { p : T.Node // T.isNode p ∧ ¬ Set.Finite (T.descendants p) } :=
      ⟨T.root, T.rootIsNode, hroot_inf⟩
    -- iterB n = stepB^n(init)
    let iterB : Nat → { p : T.Node // T.isNode p ∧ ¬ Set.Finite (T.descendants p) } :=
      fun n => Nat.rec init (fun _ prev => stepB prev) n
    -- The children relation: stepB produces a child of the input
    have hch_step : ∀ b : { p : T.Node // T.isNode p ∧ ¬ Set.Finite (T.descendants p) },
        T.children b.1 (stepB b).1 := by
      intro ⟨p, hp, hinf⟩
      exact (chosenChild_spec p hp hinf).1
    -- Extract path and prove infinite path property
    exact ⟨fun n => (iterB n).1, rfl, fun n => hch_step (iterB n)⟩

end LCS.Propositional.Infinite
end
