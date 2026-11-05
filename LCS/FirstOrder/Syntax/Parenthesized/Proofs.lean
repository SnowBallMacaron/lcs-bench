import LCS.FirstOrder.Syntax.Parenthesized

namespace LCS.FirstOrder.Syntax.Parenthesized

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax.FreeGeneration

proof_of term_free_generation := by
  -- BEGIN PROOF
    refine ⟨?_, ?_, ?_⟩
    · intro f ss us hs hu h
      let ts : Fin (L.funArity f) → Term L := fun i => Classical.choose (hs i)
      let vs : Fin (L.funArity f) → Term L := fun i => Classical.choose (hu i)
      have hts : (fun i => termPrint (ts i)) = ss :=
        funext fun i => Classical.choose_spec (hs i)
      have hvs : (fun i => termPrint (vs i)) = us :=
        funext fun i => Classical.choose_spec (hu i)
      have hprint : termPrint (Term.func f ts) =
          termPrint (Term.func f vs) := by
        change functionString f (fun i => termPrint (ts i)) =
          functionString f (fun i => termPrint (vs i))
        rw [hts, hvs]
        exact h
      have hargs : ts = vs :=
        term_func_injective f ts vs (termPrint_injective _ _ hprint)
      calc
        ss = (fun i => termPrint (ts i)) := hts.symm
        _ = (fun i => termPrint (vs i)) := by rw [hargs]
        _ = us := hvs
    · intro f g hfg ss us _ _ h
      apply hfg
      simpa [functionString] using congrArg List.head? h
    · intro f ss
      constructor
      · intro n; simp [functionString]
      · intro c; simp [functionString]


proof_of formula_free_generation := by
  -- BEGIN PROOF
    let build (op : FormulaFormationFn.Op) : (Fin op.arity → Formula L) → Formula L :=
      match op with
      | .conj => fun args => .conj (args 0) (args 1)
      | .disj => fun args => .disj (args 0) (args 1)
      | .impl => fun args => .impl (args 0) (args 1)
      | .equiv => fun args => .equiv_ (args 0) (args 1)
      | .neg => fun args => .neg (args 0)
      | .all i => fun args => .all i (args 0)
      | .ex i => fun args => .ex i (args 0)
    have hprint (op : FormulaFormationFn.Op) (args : Fin op.arity → Formula L) :
        formulaPrint (build op args) =
          applyFormulaOp op (fun i => formulaPrint (args i)) := by
      cases op <;> simp [build, formulaPrint, applyFormulaOp, vec2]
    have hop (op other : FormulaFormationFn.Op)
        (args : Fin op.arity → Formula L) (more : Fin other.arity → Formula L)
        (h : build op args = build other more) : op = other := by
      cases op <;> cases other <;> simp_all [build]
    have hinj (op : FormulaFormationFn.Op) (args more : Fin op.arity → Formula L)
        (h : build op args = build op more) : args = more := by
      cases op <;> simp only [build, Formula.conj.injEq, Formula.disj.injEq,
        Formula.impl.injEq, Formula.equiv_.injEq, Formula.neg.injEq,
        Formula.all.injEq, Formula.ex.injEq, true_and] at h
      all_goals
        funext i
        rcases i with ⟨i, hi⟩
        simp only [FormulaFormationFn.Op.arity] at hi
        match i with
        | 0 => first | exact h.1 | exact h
        | 1 => first | exact h.2 | omega
        | n + 2 => omega
    have hnonatomic (op : FormulaFormationFn.Op) (args : Fin op.arity → Formula L) :
        ¬ (build op args).isAtomic := by
      cases op <;> simp [build, Formula.isAtomic]
    have represent (op : FormulaFormationFn.Op) (ss : Fin op.arity → List (Symbol L))
        (hs : ∀ i, ∃ A : Formula L, formulaPrint A = ss i) :
        ∃ args : Fin op.arity → Formula L,
          (∀ i, formulaPrint (args i) = ss i) ∧
          formulaPrint (build op args) = applyFormulaOp op ss := by
      let args i := Classical.choose (hs i)
      have ha : ∀ i, formulaPrint (args i) = ss i :=
        fun i => Classical.choose_spec (hs i)
      refine ⟨args, ha, ?_⟩
      rw [hprint, funext ha]
    refine ⟨?_, ?_, ?_⟩
    · intro op ss us hs hu h
      obtain ⟨args, ha, hp⟩ := represent op ss hs
      obtain ⟨more, hm, hq⟩ := represent op us hu
      have ht := formulaPrint_injective (build op args) (build op more)
        (hp.trans (h.trans hq.symm))
      have he := hinj op args more ht
      funext i
      rw [← ha i, ← hm i, he]
    · intro op other hne ss us hs hu h
      obtain ⟨args, _, hp⟩ := represent op ss hs
      obtain ⟨more, _, hq⟩ := represent other us hu
      exact hne (hop op other args more
        (formulaPrint_injective _ _ (hp.trans (h.trans hq.symm))))
    · intro op ss hs A hA h
      obtain ⟨args, _, hp⟩ := represent op ss hs
      have he := formulaPrint_injective _ _ (hp.trans h)
      exact hnonatomic op args (he.symm ▸ hA)


end LCS.FirstOrder.Syntax.Parenthesized
