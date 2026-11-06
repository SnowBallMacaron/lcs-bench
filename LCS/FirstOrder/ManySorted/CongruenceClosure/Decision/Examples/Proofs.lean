import LCS.FirstOrder.ManySorted.CongruenceClosure.Decision.Examples

section

namespace LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

open LCS.FirstOrder.ManySorted

open LCS.FirstOrder.ManySorted.Semantics

open LCS.FirstOrder.ManySorted.Equality

open LCS.FirstOrder.ManySorted.CongruenceClosure

open LCS.Propositional.Semantics

proof_of node_eq_of_val_eq := Subtype.ext h
  -- BEGIN PROOF

proof_of exampleNode_mem := by
  -- REPAIR(T10-71): proof pending — verify membership of the six displayed subterms.
  sorry

proof_of exampleGraphNodes_exact := by
  -- REPAIR(T10-71): proof pending — prove the six-node enumeration is exhaustive and injective.
  sorry

proof_of exampleTermFibers_exact := by
  -- REPAIR(T10-71): proof pending — identify both term-set fibers.
  sorry

proof_of exampleE_exact := by
  -- REPAIR(T10-71): proof pending — extract the sole positive equation from the conjunction.
  sorry

proof_of exampleClosureClasses := by
  -- REPAIR(T10-72): proof pending — prove closure equals the displayed four-block partition.
  sorry

proof_of exampleGraphLabels := by
  cases n <;> rfl

proof_of exampleGraphPorts := by
  cases n <;> rfl

proof_of exampleClosurePairs := by
  -- BEGIN PROOF
    -- Make the four nodes concrete by substituting their underlying values,
    -- so that `Lambda`, `delta`, `successorOfNode` all reduce.
    obtain ⟨pfabv, pfabm⟩ := pfab
    obtain ⟨pcv, pcm⟩ := pc
    obtain ⟨pgfabav, pgfabam⟩ := pgfaba
    obtain ⟨pgcav, pgcam⟩ := pgca
    simp only at hpfab hpc hpgfaba hpgca
    subst hpfab; subst hpc; subst hpgfaba; subst hpgca
    -- The positive equation `f(a,b) =̇_s c` is a conjunct of C, so the seed
    -- relation `E` already relates `pfab` and `pc`.
    have hEfab : exampleE ⟨⟨ExampleSort.s, exampleTerm_fab⟩, pfabm⟩
        ⟨⟨ExampleSort.s, exampleTerm_c⟩, pcm⟩ := by
      refine ⟨rfl, ExampleSort.s, exampleTerm_fab, exampleTerm_c, ?_, rfl, rfl⟩
      -- msConjunctContains C (eq_ rfl s fab c): it is the left conjunct.
      exact Or.inr (Or.inl rfl)
    have hfab : msCongruenceClosure (graphOfConjunction exampleConjunction)
        exampleE (positiveEquationRelation_sortSupported exampleConjunction) _ _ :=
      msCongruenceClosure_contains _ exampleE (positiveEquationRelation_sortSupported exampleConjunction) _ _ hEfab
    refine ⟨hfab, ?_⟩
    -- For `g(f(a,b),a) ~ g(c,a)` use backward closure (2b): same label `g`,
    -- and successors `f(a,b) ~ c` (from `hfab`) and `a ~ a` (reflexivity).
    have hrefl := (positiveClosure_equivalence exampleConjunction).refl
    have hbc2b := (msCongruenceClosure_isCongruence
      (graphOfConjunction exampleConjunction) exampleE
      (positiveEquationRelation_sortSupported exampleConjunction)).2.2.2
    -- The labels of both g-nodes are `ConjSymbol.func g` (definitional now).
    have hlab : (graphOfConjunction exampleConjunction).Lambda
          ⟨⟨ExampleSort.s, exampleTerm_gfaba⟩, pgfabam⟩
        = (graphOfConjunction exampleConjunction).Lambda
          ⟨⟨ExampleSort.s, exampleTerm_gca⟩, pgcam⟩ := rfl
    refine hbc2b _ _ hlab ?_
    intro i
    -- Case on the value of `i` (g has arity length 2).
    rcases i with ⟨iv, hiv⟩
    have hlen : iv < 2 := hiv
    rcases iv with _ | _ | iv
    · -- successor 0 of both nodes: f(a,b) and c, related by `hfab`.
      -- The successor nodes reduce definitionally; relate via `hfab`.
      have hp : ((graphOfConjunction exampleConjunction).delta
          ⟨⟨ExampleSort.s, exampleTerm_gfaba⟩, pgfabam⟩ ⟨0, hiv⟩)
          = ⟨⟨ExampleSort.s, exampleTerm_fab⟩, pfabm⟩ := node_eq_of_val_eq rfl
      have hq : ((graphOfConjunction exampleConjunction).delta
          ⟨⟨ExampleSort.s, exampleTerm_gca⟩, pgcam⟩ (hlab ▸ ⟨0, hiv⟩))
          = ⟨⟨ExampleSort.s, exampleTerm_c⟩, pcm⟩ := node_eq_of_val_eq rfl
      rw [hp, hq]; exact hfab
    · -- successor 1 of both nodes: `a`, related by reflexivity.
      have hpq : ((graphOfConjunction exampleConjunction).delta
          ⟨⟨ExampleSort.s, exampleTerm_gfaba⟩, pgfabam⟩ ⟨1, hiv⟩)
          = ((graphOfConjunction exampleConjunction).delta
          ⟨⟨ExampleSort.s, exampleTerm_gca⟩, pgcam⟩ (hlab ▸ ⟨1, hiv⟩)) :=
        node_eq_of_val_eq rfl
      rw [hpq]; exact hrefl _
    · -- iv ≥ 2 is impossible.
      omega

proof_of exampleCandidateTable :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

proof_of exampleConjunction_contains_neg := Or.inr (Or.inr rfl)
  -- BEGIN PROOF

proof_of exampleTerm_gfaba_mem := ⟨rfl, ExampleSort.s, exampleTerm_gfaba, exampleTerm_gca,
  -- BEGIN PROOF
      Or.inr exampleConjunction_contains_neg, Or.inl (msTermSubterms_self _)⟩

proof_of exampleTerm_gca_mem := ⟨rfl, ExampleSort.s, exampleTerm_gfaba, exampleTerm_gca,
  -- BEGIN PROOF
      Or.inr exampleConjunction_contains_neg, Or.inr (msTermSubterms_self _)⟩

proof_of exampleTerm_fab_mem := ⟨rfl, ExampleSort.s, exampleTerm_fab, exampleTerm_c,
  -- BEGIN PROOF
      Or.inl (Or.inr (Or.inl rfl)), Or.inl (msTermSubterms_self _)⟩

proof_of exampleTerm_c_mem := ⟨rfl, ExampleSort.s, exampleTerm_fab, exampleTerm_c,
  -- BEGIN PROOF
      Or.inl (Or.inr (Or.inl rfl)), Or.inr (msTermSubterms_self _)⟩

proof_of exampleCollision := by
  -- BEGIN PROOF
    -- The four relevant nodes of `G(C)`.
    refine ⟨rfl, exampleTerm_gfaba, exampleTerm_gca,
      ⟨⟨ExampleSort.s, exampleTerm_gfaba⟩, exampleTerm_gfaba_mem⟩,
      ⟨⟨ExampleSort.s, exampleTerm_gca⟩, exampleTerm_gca_mem⟩,
      exampleConjunction_contains_neg, rfl, rfl, ?_⟩
    -- The closure relates the two g-nodes (`exampleClosurePairs`, part 2),
    -- using the f-node and c-node as the related successors of index 0.
    exact (exampleClosurePairs
      ⟨⟨ExampleSort.s, exampleTerm_fab⟩, exampleTerm_fab_mem⟩
      ⟨⟨ExampleSort.s, exampleTerm_c⟩, exampleTerm_c_mem⟩
      ⟨⟨ExampleSort.s, exampleTerm_gfaba⟩, exampleTerm_gfaba_mem⟩
      ⟨⟨ExampleSort.s, exampleTerm_gca⟩, exampleTerm_gca_mem⟩
      rfl rfl rfl rfl).2

proof_of exampleDecision := by
  -- BEGIN PROOF
    -- The collision on the negated equation `¬(g(f(a,b),a) =̇ g(c,a))` yields
    -- unsatisfiability via the soundness direction of Lemma 10.6.2.
    obtain ⟨hL, r, v, p, q, hneg, hp, hq, hcol⟩ := exampleCollision
    exact collision_unsat_direction exampleConjunction
      ⟨hL, ExampleSort.s, r, v, p, q, hneg, hp, hq, hcol⟩

end LCS.FirstOrder.ManySorted.CongruenceClosure.Decision

end
