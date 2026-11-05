import LCS.FirstOrder.Syntax.FreeGeneration.Part2

section

namespace LCS.FirstOrder.Syntax.FreeGeneration

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

helper /-- Helper: K of a proper prefix of a list of mapped term symbol lists ≤ n-1. -/
theorem formulaListK_term_prefix_le {L : Language}
    (n : Nat) (ts : Fin n → Term L)
    (w rest : List (FormulaSymbol L))
    (hw : (List.ofFn (fun i =>
        (Term.toSymbolList (ts i)).map FormulaSymbol.termSym)).flatten = w ++ rest)
    (hne : rest ≠ []) :
    formulaListK L w ≤ ↑n - 1 := by
-- BEGIN PROOF
  induction n generalizing w rest with
  | zero =>
    simp [List.ofFn, List.flatten] at hw
    exact absurd (by cases w <;> simpa using hw) hne
  | succ m ihm =>
    rw [List.ofFn_succ, List.flatten_cons] at hw
    by_cases hlen : w.length < ((Term.toSymbolList (ts 0)).map FormulaSymbol.termSym).length
    · -- w is a strict prefix of the first mapped term
      obtain ⟨mid, hmid_t, _⟩ := list_split_left hw.symm (by omega)
      have hmid_ne : mid ≠ [] := by
        intro h; subst h; simp at hmid_t; rw [hmid_t] at hlen; simp at hlen
      have := formulaListK_mapped_prefix_le_zero (ts 0) w mid hmid_t hmid_ne
      push_cast; omega
    · -- w extends past the first mapped term
      obtain ⟨mid, hmid_w, hmid_b⟩ := list_split_left hw (by omega)
      rw [hmid_w, formulaListK_append, formulaListK_map_termSym, termListK_toSymbolList]
      have := ihm (fun i => ts i.succ) mid rest hmid_b.symm hne
      push_cast; omega

helper /-- Helper for binary connective cases of formula_prefix_k_le_zero.
    Covers conj, disj, impl, equiv_ whose symbol lists have the form
    [lParen] ++ toSymbolList A ++ [conn] ++ toSymbolList B ++ [rParen]
    where conn has K = -1. -/
theorem binary_connective_prefix_k_le_zero {L : Language}
    (A B : Formula L)
    (conn : FormulaSymbol L)
    (hconnK : formulaSymbolK L conn = -1)
    (ihA : ∀ (w rest : List (FormulaSymbol L)),
      Formula.toSymbolList A = w ++ rest → rest ≠ [] → formulaListK L w ≤ 0)
    (ihB : ∀ (w rest : List (FormulaSymbol L)),
      Formula.toSymbolList B = w ++ rest → rest ≠ [] → formulaListK L w ≤ 0)
    (w rest : List (FormulaSymbol L))
    (hw : [FormulaSymbol.lParen] ++ Formula.toSymbolList A ++ [conn] ++
      Formula.toSymbolList B ++ [FormulaSymbol.rParen] = w ++ rest)
    (hne : rest ≠ []) :
    formulaListK L w ≤ 0 := by
-- BEGIN PROOF
  cases w with
  | nil => simp [formulaListK]
  | cons x xs =>
    have hx : x = FormulaSymbol.lParen := by
      have := List.head_eq_of_cons_eq hw.symm; simpa using this
    subst hx
    rw [formulaListK]; simp only [formulaSymbolK]
    suffices h : formulaListK L xs ≤ 1 by omega
    have htl : xs ++ rest = Formula.toSymbolList A ++ [conn] ++
        Formula.toSymbolList B ++ [FormulaSymbol.rParen] := by
      have := List.tail_eq_of_cons_eq hw.symm; simpa using this
    have htl_ra : xs ++ rest = Formula.toSymbolList A ++
        ([conn] ++ Formula.toSymbolList B ++ [FormulaSymbol.rParen]) := by
      simp [List.append_assoc] at htl ⊢; exact htl
    by_cases hlen : xs.length < (Formula.toSymbolList A).length
    · -- xs is a strict prefix of toSymbolList A
      obtain ⟨mid, hmid_eq, _⟩ := list_split_left htl_ra (by omega)
      have hmid_ne : mid ≠ [] := by
        intro heq; subst heq; simp at hmid_eq
        have := congrArg List.length hmid_eq; omega
      have h1 := ihA xs mid hmid_eq hmid_ne; omega
    · -- xs extends past or equals toSymbolList A
      obtain ⟨mid, hmid_xs, hmid_rest⟩ := list_split_left htl_ra.symm (by omega)
      rw [hmid_xs, formulaListK_append, formulaListK_toSymbolList]
      suffices h2 : formulaListK L mid ≤ 0 by omega
      cases mid with
      | nil => simp [formulaListK]
      | cons y ys =>
        have hy : y = conn := by
          have := List.head_eq_of_cons_eq hmid_rest; simpa using this
        subst hy
        rw [formulaListK, hconnK]
        suffices h3 : formulaListK L ys ≤ 1 by omega
        have hys_rest : ys ++ rest = Formula.toSymbolList B ++
            [FormulaSymbol.rParen] := by
          have := List.tail_eq_of_cons_eq hmid_rest; simpa using this
        by_cases hlen2 : ys.length < (Formula.toSymbolList B).length
        · -- ys is a strict prefix of toSymbolList B
          obtain ⟨mid2, hmid2_eq, _⟩ := list_split_left hys_rest (by omega)
          have hmid2_ne : mid2 ≠ [] := by
            intro heq; subst heq; simp at hmid2_eq
            have := congrArg List.length hmid2_eq; omega
          have h4 := ihB ys mid2 hmid2_eq hmid2_ne; omega
        · -- ys extends past or equals toSymbolList B
          obtain ⟨mid2, hmid2_ys, hmid2_rest⟩ :=
            list_split_left hys_rest.symm (by omega)
          rw [hmid2_ys, formulaListK_append, formulaListK_toSymbolList]
          cases mid2 with
          | nil => simp [formulaListK]
          | cons z zs =>
            exfalso; apply hne
            simp at hmid2_rest
            exact hmid2_rest.2.2

proof_of formula_prefix_k_le_zero := by
  -- BEGIN PROOF
    induction A generalizing w rest with
    | falsum =>
      simp at hw
      cases w with
      | nil => simp [formulaListK]
      | cons x xs =>
        have : xs ++ rest = [] := by have := List.tail_eq_of_cons_eq hw; simpa using this
        exact absurd (by cases xs <;> simpa using this) hne
    | pred0 P hP =>
      simp at hw
      cases w with
      | nil => simp [formulaListK]
      | cons x xs =>
        have : xs ++ rest = [] := by have := List.tail_eq_of_cons_eq hw; simpa using this
        exact absurd (by cases xs <;> simpa using this) hne
    | predN P hP ts =>
      simp only [Formula.toSymbolList_predN, List.singleton_append] at hw
      cases w with
      | nil => simp [formulaListK]
      | cons x xs =>
        have hx := List.head_eq_of_cons_eq hw
        have htl : (List.ofFn (fun i =>
            (Term.toSymbolList (ts i)).map FormulaSymbol.termSym)).flatten = xs ++ rest := by
          have := List.tail_eq_of_cons_eq hw; simpa using this
        subst hx
        rw [formulaListK]; simp only [formulaSymbolK]
        have := formulaListK_term_prefix_le (L.predArity P) ts xs rest htl hne
        omega
    | eq_ _ t1 t2 =>
      -- toSymbolList = [eqSym] ++ map termSym (toSymbolList t1) ++ map termSym (toSymbolList t2)
      -- Same pattern as predN: eqSym has K = -1, then two mapped term lists.
      simp only [Formula.toSymbolList_eq, List.singleton_append] at hw
      cases w with
      | nil => simp [formulaListK]
      | cons x xs =>
        have hx := List.head_eq_of_cons_eq hw
        have htl : (Term.toSymbolList t1).map FormulaSymbol.termSym ++
            (Term.toSymbolList t2).map FormulaSymbol.termSym = xs ++ rest := by
          have := List.tail_eq_of_cons_eq hw; simpa using this
        subst hx
        rw [formulaListK]; simp only [formulaSymbolK]
        -- xs is a proper prefix of map(t1) ++ map(t2); need K(xs) ≤ 1
        -- Case split on where xs falls in map(t1) ++ map(t2)
        by_cases hlen : xs.length < ((Term.toSymbolList t1).map FormulaSymbol.termSym).length
        · -- xs is a strict prefix of map(t1)
          obtain ⟨mid, hmid_t, _⟩ := list_split_left htl.symm (by omega)
          have hmid_ne : mid ≠ [] := by
            intro h; subst h; simp at hmid_t; rw [hmid_t] at hlen; simp at hlen
          have := formulaListK_mapped_prefix_le_zero t1 xs mid hmid_t hmid_ne
          omega
        · -- xs extends past map(t1)
          obtain ⟨mid, hmid_w, hmid_b⟩ := list_split_left htl (by omega)
          rw [hmid_w, formulaListK_append, formulaListK_map_termSym, termListK_toSymbolList]
          -- mid ++ rest = map(t2), so mid is a proper prefix of map(t2)
          have := formulaListK_mapped_prefix_le_zero t2 mid rest hmid_b.symm hne
          omega
    | conj A B ihA ihB =>
      simp only [Formula.toSymbolList_conj] at hw
      exact binary_connective_prefix_k_le_zero A B .connAnd rfl ihA ihB w rest hw hne
    | disj A B ihA ihB =>
      simp only [Formula.toSymbolList_disj] at hw
      exact binary_connective_prefix_k_le_zero A B .connOr rfl ihA ihB w rest hw hne
    | impl A B ihA ihB =>
      simp only [Formula.toSymbolList_impl] at hw
      exact binary_connective_prefix_k_le_zero A B .connImpl rfl ihA ihB w rest hw hne
    | equiv_ A B ihA ihB =>
      simp only [Formula.toSymbolList_equiv] at hw
      exact binary_connective_prefix_k_le_zero A B .connEquiv rfl ihA ihB w rest hw hne
    | neg A ihA =>
      simp only [Formula.toSymbolList_neg] at hw
      cases w with
      | nil => simp [formulaListK]
      | cons x xs =>
        have hx := List.head_eq_of_cons_eq hw
        have htl : Formula.toSymbolList A = xs ++ rest := by
          have := List.tail_eq_of_cons_eq hw; simpa using this
        subst hx
        rw [formulaListK]; simp only [formulaSymbolK]
        have := ihA xs rest htl hne; omega
    | all i A ihA =>
      simp only [Formula.toSymbolList_all] at hw
      cases w with
      | nil => simp [formulaListK]
      | cons x xs =>
        have hx := List.head_eq_of_cons_eq hw
        subst hx
        rw [formulaListK]; simp only [formulaSymbolK]
        suffices formulaListK L xs ≤ 1 by omega
        have htl : FormulaSymbol.varSym_ i :: Formula.toSymbolList A = xs ++ rest := by
          have := List.tail_eq_of_cons_eq hw; simpa using this
        cases xs with
        | nil => simp [formulaListK]
        | cons y ys =>
          have hy := List.head_eq_of_cons_eq htl.symm; subst hy
          rw [formulaListK]; simp only [formulaSymbolK]
          have htl2 : ys ++ rest = Formula.toSymbolList A := by
            have := List.tail_eq_of_cons_eq htl.symm; simpa using this
          have := ihA ys rest htl2.symm hne; omega
    | ex i A ihA =>
      simp only [Formula.toSymbolList_ex] at hw
      cases w with
      | nil => simp [formulaListK]
      | cons x xs =>
        have hx := List.head_eq_of_cons_eq hw
        subst hx
        rw [formulaListK]; simp only [formulaSymbolK]
        suffices formulaListK L xs ≤ 1 by omega
        have htl : FormulaSymbol.varSym_ i :: Formula.toSymbolList A = xs ++ rest := by
          have := List.tail_eq_of_cons_eq hw; simpa using this
        cases xs with
        | nil => simp [formulaListK]
        | cons y ys =>
          have hy := List.head_eq_of_cons_eq htl.symm; subst hy
          rw [formulaListK]; simp only [formulaSymbolK]
          have htl2 : ys ++ rest = Formula.toSymbolList A := by
            have := List.tail_eq_of_cons_eq htl.symm; simpa using this
          have := ihA ys rest htl2.symm hne; omega


proof_of formula_prefix_free := by
  -- BEGIN PROOF
    intro ⟨B, hB⟩
    have hk_w := formulaListK_toSymbolList B
    rw [hB] at hk_w
    have hk_le := formula_prefix_k_le_zero A w rest hw hne
    omega


helper /-- Representative formula-constructor disjointness cases: falsum ≠ neg,
conj ≠ disj, conj ≠ all. Proof-body helper for `formula_free_generation`. -/
theorem formula_noConfusion {L : Language} :
    (∀ (A : Formula L), Formula.falsum ≠ Formula.neg A) ∧
    (∀ (A B C D : Formula L),
      Formula.conj A B ≠ Formula.disj C D) ∧
    (∀ (A B : Formula L) (i : Nat),
      Formula.conj A B ≠ Formula.all i A) :=
-- BEGIN PROOF
by
  constructor
  · intro A h; cases h
  constructor
  · intro A B C D h; cases h
  · intro A B i h; cases h

helper /-- Conjunction-constructor injectivity: if conj A1 B1 = conj A2 B2 then
A1 = A2 and B1 = B2. Proof-body helper for `formula_free_generation`. -/
theorem formula_conj_injective {L : Language}
    (A1 A2 B1 B2 : Formula L)
    (h : Formula.conj A1 B1 = Formula.conj A2 B2) :
    A1 = A2 ∧ B1 = B2 :=
-- BEGIN PROOF
by
  injection h with h1 h2
  exact ⟨h1, h2⟩

helper /-- Universal-quantifier-constructor injectivity: if all i A = all j B
then i = j and A = B. Proof-body helper for `formula_free_generation`. -/
theorem formula_all_injective {L : Language}
    (i j : Nat) (A B : Formula L)
    (h : Formula.all i A = Formula.all j B) :
    i = j ∧ A = B :=
-- BEGIN PROOF
by
  injection h with h1 h2
  exact ⟨h1, h2⟩







proof_of term_free_generation := by
  -- BEGIN PROOF
    refine ⟨?_, ?_, ?_⟩
    · intro f ss us hs hu h
      let ts : Fin (L.funArity f) → Term L := fun i => Classical.choose (hs i)
      let vs : Fin (L.funArity f) → Term L := fun i => Classical.choose (hu i)
      have hts : (fun i => Term.toSymbolList (ts i)) = ss :=
        funext fun i => Classical.choose_spec (hs i)
      have hvs : (fun i => Term.toSymbolList (vs i)) = us :=
        funext fun i => Classical.choose_spec (hu i)
      have hprint : Term.toSymbolList (Term.func f ts) =
          Term.toSymbolList (Term.func f vs) := by
        change TermFormationFn.c_f f (fun i => Term.toSymbolList (ts i)) =
          TermFormationFn.c_f f (fun i => Term.toSymbolList (vs i))
        rw [hts, hvs]
        exact h
      have hargs : ts = vs :=
        term_func_injective f ts vs (term_toSymbolList_injective _ _ hprint)
      calc
        ss = (fun i => Term.toSymbolList (ts i)) := hts.symm
        _ = (fun i => Term.toSymbolList (vs i)) := by rw [hargs]
        _ = us := hvs
    · intro f g hfg ss us _ _ h
      apply hfg
      simpa [TermFormationFn.c_f] using congrArg List.head? h
    · intro f ss
      constructor
      · intro n; simp [TermFormationFn.c_f]
      · intro c; simp [TermFormationFn.c_f]








helper /-- Non-atomic formula constructors increase the connective/quantifier
count: each of C_∧, C_∨, C_⊃, C_≡, C_¬, A_i, E_i produces a formula
whose `sizeOf` strictly exceeds those of its formula inputs. Proof-body
helper for the size-increasing clauses of `formula_free_generation`. -/
theorem formula_sizeOf_constructor_gt {L : Language} :
    (∀ (A B : Formula L),
      sizeOf A < sizeOf (Formula.conj A B) ∧
      sizeOf B < sizeOf (Formula.conj A B)) ∧
    (∀ (A B : Formula L),
      sizeOf A < sizeOf (Formula.disj A B) ∧
      sizeOf B < sizeOf (Formula.disj A B)) ∧
    (∀ (A B : Formula L),
      sizeOf A < sizeOf (Formula.impl A B) ∧
      sizeOf B < sizeOf (Formula.impl A B)) ∧
    (∀ (A B : Formula L),
      sizeOf A < sizeOf (Formula.equiv_ A B) ∧
      sizeOf B < sizeOf (Formula.equiv_ A B)) ∧
    (∀ (A : Formula L),
      sizeOf A < sizeOf (Formula.neg A)) ∧
    (∀ (i : Nat) (A : Formula L),
      sizeOf A < sizeOf (Formula.all i A)) ∧
    (∀ (i : Nat) (A : Formula L),
      sizeOf A < sizeOf (Formula.ex i A)) :=
-- BEGIN PROOF
by
  refine ⟨fun A B => ⟨by simp [Formula.conj.sizeOf_spec]; omega,
                       by simp [Formula.conj.sizeOf_spec]; omega⟩,
          fun A B => ⟨by simp [Formula.disj.sizeOf_spec]; omega,
                       by simp [Formula.disj.sizeOf_spec]; omega⟩,
          fun A B => ⟨by simp [Formula.impl.sizeOf_spec]; omega,
                       by simp [Formula.impl.sizeOf_spec]; omega⟩,
          fun A B => ⟨by simp [Formula.equiv_.sizeOf_spec]; omega,
                       by simp [Formula.equiv_.sizeOf_spec]; omega⟩,
          fun A => by simp [Formula.neg.sizeOf_spec],
          fun i A => by simp [Formula.all.sizeOf_spec]; omega,
          fun i A => by simp [Formula.ex.sizeOf_spec]; omega⟩

end LCS.FirstOrder.Syntax.FreeGeneration

end

section

namespace LCS.FirstOrder.Syntax.FreeGeneration

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

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
        Formula.toSymbolList (build op args) =
          op.apply (fun i => Formula.toSymbolList (args i)) := by
      cases op <;> rfl
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
    have represent (op : FormulaFormationFn.Op) (ss : Fin op.arity → List (FormulaSymbol L))
        (hs : ∀ i, ∃ A : Formula L, Formula.toSymbolList A = ss i) :
        ∃ args : Fin op.arity → Formula L,
          (∀ i, Formula.toSymbolList (args i) = ss i) ∧
          Formula.toSymbolList (build op args) = op.apply ss := by
      let args i := Classical.choose (hs i)
      have ha : ∀ i, Formula.toSymbolList (args i) = ss i :=
        fun i => Classical.choose_spec (hs i)
      refine ⟨args, ha, ?_⟩
      rw [hprint, funext ha]
    refine ⟨?_, ?_, ?_⟩
    · intro op ss us hs hu h
      obtain ⟨args, ha, hp⟩ := represent op ss hs
      obtain ⟨more, hm, hq⟩ := represent op us hu
      have ht := formula_constructor_range_distinguishable (build op args) (build op more)
        (hp.trans (h.trans hq.symm))
      have he := hinj op args more ht
      funext i
      rw [← ha i, ← hm i, he]
    · intro op other hne ss us hs hu h
      obtain ⟨args, _, hp⟩ := represent op ss hs
      obtain ⟨more, _, hq⟩ := represent other us hu
      exact hne (hop op other args more
        (formula_constructor_range_distinguishable _ _ (hp.trans (h.trans hq.symm))))
    · intro op ss hs A hA h
      obtain ⟨args, _, hp⟩ := represent op ss hs
      have he := formula_constructor_range_distinguishable _ _ (hp.trans h)
      exact hnonatomic op args (he.symm ▸ hA)


end LCS.FirstOrder.Syntax.FreeGeneration

end
