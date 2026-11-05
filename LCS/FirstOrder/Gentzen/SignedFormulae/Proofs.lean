import LCS.FirstOrder.Gentzen.SignedFormulae

namespace LCS.FirstOrder.Gentzen.SignedFormulae

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.Gentzen

proof_of isTermAlgebra_iff_constructorOperations := by
  constructor
  · intro hAlg
    exact ⟨(fun c => ⟨Term.const c, hAlg.closedConst c⟩),
      (fun f ts => ⟨Term.func f (fun i => (ts i).val),
        hAlg.closedFunc f _ (fun i => (ts i).property)⟩),
      (fun _ => rfl), (fun _ _ => rfl)⟩
  · rintro ⟨constH, funcH, hConst, hFunc⟩
    refine ⟨hH, ?_, ?_⟩
    · intro f ts hts
      have h := (funcH f (fun i => ⟨ts i, hts i⟩)).property
      rw [hFunc] at h
      exact h
    · intro c
      have h := (constH c).property
      rw [hConst] at h
      exact h


proof_of termAlgebra_infinite := by
  obtain ⟨t₀, ht₀⟩ := hH.nonempty
  let iter : Nat → Term L := Nat.rec t₀ (fun _ t => Term.func f (fun _ => t))
  have hmem : ∀ n, iter n ∈ H := by
    intro n
    induction n with
    | zero => exact ht₀
    | succ n ih => exact hH.closedFunc f (fun _ => iter n) (fun _ => ih)
  have hsize : ∀ n, n ≤ Syntax.FreeGeneration.termSize (iter n) := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have hlt := Syntax.FreeGeneration.term_sizeOf_func_gt f
        (fun _ => iter n) ⟨0, hf⟩
      change Syntax.FreeGeneration.termSize (iter n) <
        Syntax.FreeGeneration.termSize (iter (n + 1)) at hlt
      omega
  rintro ⟨n, e, hcover⟩
  let bound := (List.ofFn (fun i => Syntax.FreeGeneration.termSize (e i))).foldl (· + ·) 0
  obtain ⟨i, hi⟩ := hcover (iter (bound + 1)) (hmem (bound + 1))
  have hbound := Syntax.FreeGeneration.foldl_ofFn_ge_elem e i
  change Syntax.FreeGeneration.termSize (e i) ≤ bound at hbound
  rw [hi] at hbound
  have hlarge := hsize (bound + 1)
  omega


helper /-- Definition 5.4.5 (contrapositive of the infinitude remark): A term
algebra admitting a finite cover has no positive-arity function symbol. -/
theorem termAlgebra_finite_no_positive_arity {L : Language} {H : Set (Term L)}
    (hH : IsTermAlgebra L H)
    (hfinite : ∃ (n : Nat) (e : Fin n → Term L), ∀ t ∈ H, ∃ i, e i = t) :
    ¬ ∃ f : L.funSymbols, 0 < L.funArity f := by
  rintro ⟨f, hf⟩
  exact termAlgebra_infinite f hf hH hfinite



helper /-- Definition 5.4.7 (companion): Include a term of L_S into the ambient language
by forgetting the occurrence proofs on its symbols. -/
def reductTermInclusion {L : Language} (S : Set (SignedFormula L)) :
    Term (reductLanguage L S) → Term L
  | .var x => .var x
  | .const c => .const c.val
  | .func f ts => .func f.val (fun i => reductTermInclusion S (ts i))



helper /-- A term lies in the image of the reduct inclusion exactly when all its
function and constant symbols occur in S. -/
theorem exists_reductTerm_iff {L : Language} (S : Set (SignedFormula L))
    (t : Term L) :
    (∃ u, reductTermInclusion S u = t) ↔
      termFunSyms t ⊆ signedSetFunSyms S ∧ termConstSyms t ⊆ signedSetConstSyms S := by
  classical
  constructor
  · rintro ⟨u, rfl⟩
    induction u with
    | var x =>
      constructor
      · intro f h; exact False.elim h
      · intro c h; cases h
    | const c =>
      constructor
      · intro f h; exact False.elim h
      · intro d h
        have hd : d = c.val := by
          simpa [reductTermInclusion, termConstSyms, termConstsList] using h
        exact hd ▸ c.property
    | func f ts ih =>
      constructor
      · intro g hg
        rcases hg with rfl | ⟨i, hi⟩
        · exact f.property
        · exact (ih i).1 g hi
      · intro c hc
        obtain ⟨i, hi⟩ := (termConstSyms_func_iff f.val
          (fun i => reductTermInclusion S (ts i)) c).mp hc
        exact (ih i).2 c hi
  · induction t with
    | var x => intro _; exact ⟨.var x, rfl⟩
    | const c =>
      intro h
      have hc : c ∈ signedSetConstSyms S := h.2 c (by
        show Term.const c ∈ [Term.const c]
        exact List.mem_cons_self)
      exact ⟨.const ⟨c, hc⟩, rfl⟩
    | func f ts ih =>
      intro h
      have hf : f ∈ signedSetFunSyms S := h.1 f (Or.inl rfl)
      have hArgs : ∀ i, ∃ u, reductTermInclusion S u = ts i := by
        intro i
        apply ih i
        constructor
        · intro g hg; exact h.1 g (Or.inr ⟨i, hg⟩)
        · intro c hc; exact h.2 c ((termConstSyms_func_iff f ts c).mpr ⟨i, hc⟩)
      refine ⟨.func ⟨f, hf⟩ (fun i => Classical.choose (hArgs i)), ?_⟩
      change Term.func f (fun i => reductTermInclusion S (Classical.choose (hArgs i))) = _
      exact congrArg (Term.func f) (funext fun i => Classical.choose_spec (hArgs i))

helper /-- Definition 5.4.7 (companion): Ambient term algebras over L_S are exactly
the images of term algebras in the reduct language under the inclusion. -/
theorem isTermAlgebraOver_iff_reduct {L : Language} (S : Set (SignedFormula L))
    (H : Set (Term L)) :
    IsTermAlgebraOver L S H ↔
      ∃ H' : Set (Term (reductLanguage L S)), IsTermAlgebra (reductLanguage L S) H' ∧
        ∀ t, t ∈ H ↔ ∃ u ∈ H', reductTermInclusion S u = t := by
  classical
  constructor
  · intro h
    let H' : Set (Term (reductLanguage L S)) := fun u => reductTermInclusion S u ∈ H
    refine ⟨H', ?_, ?_⟩
    · refine {
        nonempty := ?_
        closedFunc := fun f ts hts => h.closedFunc f.val f.property
          (fun i => reductTermInclusion S (ts i)) hts
        closedConst := fun c => h.closedConst c.val c.property }
      obtain ⟨t, ht⟩ := h.nonempty
      obtain ⟨u, hu⟩ := (exists_reductTerm_iff S t).mpr (h.symbols t ht)
      exact ⟨u, by change reductTermInclusion S u ∈ H; rw [hu]; exact ht⟩
    · intro t
      constructor
      · intro ht
        obtain ⟨u, hu⟩ := (exists_reductTerm_iff S t).mpr (h.symbols t ht)
        exact ⟨u, by change reductTermInclusion S u ∈ H; rw [hu]; exact ht, hu⟩
      · rintro ⟨u, hu, rfl⟩; exact hu
  · rintro ⟨H', hAlg, hImage⟩
    refine { nonempty := ?_, symbols := ?_, closedFunc := ?_, closedConst := ?_ }
    · obtain ⟨u, hu⟩ := hAlg.nonempty
      exact ⟨reductTermInclusion S u, (hImage _).mpr ⟨u, hu, rfl⟩⟩
    · intro t ht
      obtain ⟨u, _, hu⟩ := (hImage t).mp ht
      exact (exists_reductTerm_iff S t).mp ⟨u, hu⟩
    · intro f hf ts hts
      have hArgs := fun i => (hImage (ts i)).mp (hts i)
      let us := fun i => Classical.choose (hArgs i)
      have hus : ∀ i, us i ∈ H' := fun i => (Classical.choose_spec (hArgs i)).1
      apply (hImage _).mpr
      refine ⟨.func ⟨f, hf⟩ us, hAlg.closedFunc ⟨f, hf⟩ us hus, ?_⟩
      change Term.func f (fun i => reductTermInclusion S (us i)) = _
      exact congrArg (Term.func f) (funext fun i => (Classical.choose_spec (hArgs i)).2)
    · intro c hc
      exact (hImage _).mpr ⟨.const ⟨c, hc⟩, hAlg.closedConst ⟨c, hc⟩, rfl⟩

helper /-- For any structure M, term t', a ground term t (whose evaluation is
assignment-independent), variable x, element m, and assignment s:
evaluating t'[t/x] under s equals evaluating t' under s[x := m],
provided t evaluates to m under all assignments. -/
theorem termSubstEvalConst {L : Language} (M : Structure L)
    (t' : Term L) (t : Term L) (x : Nat) (m : M.carrier)
    (ht : ∀ s' : Assignment M, termEval M s' t = m)
    (s : Assignment M) :
    termEval M s (termSubst t' t x) =
    termEval M (assignUpdate s x m) t' := by
-- BEGIN PROOF
  induction t' with
  | var y =>
    simp [termSubst, termEval, assignUpdate]
    split
    · subst_vars; simp [ht]
    · rfl
  | const c =>
    simp [termSubst, termEval]
  | func f ts ih =>
    simp [termSubst, termEval]
    congr 1; funext j; exact ih j

helper /-- For any structure M, FormulaN A, a ground term t, variable x,
element m, and assignment s: evaluating A[t/x] under s is equivalent
to evaluating A under s[x := m], provided t evaluates to m under all
assignments. -/
theorem formulaSubstEvalConstN {L : Language} (M : Structure L)
    (A : FormulaN L) (t : Term L) (x : Nat) (m : M.carrier)
    (ht : ∀ s' : Assignment M, termEval M s' t = m)
    (s : Assignment M) :
    formulaEvalN M (formulaSubstN A t x) s ↔
    formulaEvalN M A (assignUpdate s x m) := by
-- BEGIN PROOF
  induction A generalizing s with
  | predN P ts =>
    simp only [formulaSubstN, formulaEvalN]
    have heq : (fun i => termEval M s (termSubst (ts i) t x)) =
               (fun i => termEval M (assignUpdate s x m) (ts i)) := by
      funext j; exact termSubstEvalConst M (ts j) t x m ht s
    rw [heq]
  | eq_ _ t1 t2 =>
    simp only [formulaSubstN, formulaEvalN]
    rw [termSubstEvalConst M t1 t x m ht s, termSubstEvalConst M t2 t x m ht s]
  | conj A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN, Basic.andM]; exact and_congr (ihA s) (ihB s)
  | disj A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN, Basic.orM]; exact or_congr (ihA s) (ihB s)
  | impl A B ihA ihB =>
    simp only [formulaSubstN, formulaEvalN, Basic.implM]; exact imp_congr (ihA s) (ihB s)
  | neg A ih =>
    simp only [formulaSubstN, formulaEvalN, Basic.negM]; exact not_congr (ih s)
  | all j A ih =>
    simp only [formulaSubstN]
    by_cases hxj : x = j
    · subst hxj
      simp only [bne_self_eq_false, formulaEvalN]
      have key : ∀ (a : M.carrier),
          assignUpdate (assignUpdate s x m) x a = assignUpdate s x a :=
        fun a => funext fun k => by unfold assignUpdate; split <;> simp_all
      apply forall_congr'; intro a; rw [key]
    · simp only [show (x != j) = true from by
        rw [bne_iff_ne]; exact hxj, ite_true, formulaEvalN]
      have swap : ∀ (a : M.carrier),
          assignUpdate (assignUpdate s x m) j a =
            assignUpdate (assignUpdate s j a) x m :=
        fun a => funext fun k => by
          unfold assignUpdate; split <;> split <;> simp_all
      apply forall_congr'; intro a; rw [swap]; exact ih (assignUpdate s j a)
  | ex j A ih =>
    simp only [formulaSubstN]
    by_cases hxj : x = j
    · subst hxj
      simp only [bne_self_eq_false, formulaEvalN]
      have key : ∀ (a : M.carrier),
          assignUpdate (assignUpdate s x m) x a = assignUpdate s x a :=
        fun a => funext fun k => by unfold assignUpdate; split <;> simp_all
      apply exists_congr; intro a; rw [key]
    · simp only [show (x != j) = true from by
        rw [bne_iff_ne]; exact hxj, ite_true, formulaEvalN]
      have swap : ∀ (a : M.carrier),
          assignUpdate (assignUpdate s x m) j a =
            assignUpdate (assignUpdate s j a) x m :=
        fun a => funext fun k => by
          unfold assignUpdate; split <;> split <;> simp_all
      apply exists_congr; intro a; rw [swap]; exact ih (assignUpdate s j a)

helper theorem cast_arity_args {α : Type} {n m : Nat} (e : n = m)
    (args : Fin m → α) : (fun i => args (Fin.cast e i)) = (e ▸ args) := by
  cases e
  rfl

helper theorem cast_arity_args_cancel {α : Type} {n m : Nat} (e : n = m)
    (args : Fin m → α) : (fun i => (e ▸ args) (Fin.cast e.symm i)) = args := by
  cases e
  rfl

helper /-- Proof of Definition 5.4.6 (Note, terms): A reduct preserves term values
under assignments transported along its equality of carriers. -/
theorem termEval_mapReduct {L L' : Language} {hR : IsLanguageReduct L L'}
    {M : Structure L} {M' : Structure L'} (h : IsStructureReduct hR M M')
    (s : Assignment M) (t : Term L) :
    termEval M' (fun x => cast h.sameDomain (s x)) (Term.mapReduct hR t) =
      cast h.sameDomain (termEval M s t) := by
  rcases M with ⟨D, hn, fn, cn, pn⟩
  rcases M' with ⟨D', hn', fn', cn', pn'⟩
  rcases h with ⟨hd, hc, hf, hp⟩
  dsimp at hd
  cases hd
  dsimp at hc hf hp ⊢
  induction t with
  | var x => rfl
  | const c => exact hc c
  | func f ts ih =>
    simp only [Term.mapReduct, termEval]
    simp only [ih]
    have he : (fun i => termEval ⟨D, hn, fn, cn, pn⟩ s (ts (Fin.cast (hR.funArityCompat f) i))) =
        (hR.funArityCompat f ▸ (fun i => termEval ⟨D, hn, fn, cn, pn⟩ s (ts i))) := by
      exact cast_arity_args _ (fun i => termEval ⟨D, hn, fn, cn, pn⟩ s (ts i))
    rw [he]
    exact hf f _

proof_of exists_structureExpansion := by
  -- BEGIN PROOF
  classical
  let extend {A B : Type} (i : A → B) {Q : B → Type}
      (v : ∀ a, Q (i a)) (d : ∀ b, Q b) (b : B) : Q b :=
    if h : ∃ a, i a = b then h.choose_spec ▸ v h.choose else d b
  have extend_eq {A B : Type} (i : A → B) (hi : Function.Injective i)
      {Q : B → Type} (v : ∀ a, Q (i a)) (d : ∀ b, Q b) (a : A) :
      extend i v d (i a) = v a := by
    dsimp only [extend]
    rw [dif_pos (show ∃ a', i a' = i a from ⟨a, rfl⟩)]
    have key (a' : A) (ha' : i a' = i a) : (ha' ▸ v a') = v a := by
      have he := hi ha'
      subst a'
      rfl
    exact key _ _
  let M' : Structure L' := {
    carrier := M.carrier
    carrierNonempty := M.carrierNonempty
    interpConst := extend hR.constEmbed M.interpConst (fun _ => Classical.choice M.carrierNonempty)
    interpFunc := extend hR.funEmbed
      (fun f args => M.interpFunc f (fun i => args (Fin.cast (hR.funArityCompat f).symm i)))
      (fun _ _ => Classical.choice M.carrierNonempty)
    interpPred := extend hR.predEmbed
      (fun P args => M.interpPred P (fun i => args (Fin.cast (hR.predArityCompat P).symm i)))
      (fun _ _ => False) }
  refine ⟨M', rfl, ?_, ?_, ?_⟩
  · intro c
    dsimp only [M']
    simpa only [cast_eq] using extend_eq hR.constEmbed hR.constInj
      (Q := fun _ => M.carrier) M.interpConst (fun _ => Classical.choice M.carrierNonempty) c
  · intro f args
    dsimp only [M']
    rw [extend_eq _ hR.funInj (Q := fun f => (Fin (L'.funArity f) → M.carrier) → M.carrier)
      (fun f args => M.interpFunc f (fun i => args (Fin.cast (hR.funArityCompat f).symm i)))
      (fun _ _ => Classical.choice M.carrierNonempty) f]
    simp only [cast_eq]
    exact congrArg (M.interpFunc f) (cast_arity_args_cancel (hR.funArityCompat f) args)
  · intro P args
    dsimp only [M']
    rw [extend_eq _ hR.predInj (Q := fun P => (Fin (L'.predArity P) → M.carrier) → Prop)
      (fun P args => M.interpPred P (fun i => args (Fin.cast (hR.predArityCompat P).symm i)))
      (fun _ _ => False) P]
    simp only [cast_eq]
    have he : (fun i => (hR.predArityCompat P ▸ args) (Fin.cast (hR.predArityCompat P).symm i)) = args := by
      exact cast_arity_args_cancel (hR.predArityCompat P) args
    rw [he]

proof_of formulaEvalN_mapReduct := by
  -- BEGIN PROOF
  rcases M with ⟨D, hn, fn, cn, pn⟩
  rcases M' with ⟨D', hn', fn', cn', pn'⟩
  rcases h with ⟨hd, hc, hf, hp⟩
  dsimp at hd
  cases hd
  have ht := termEval_mapReduct (M := ⟨D, hn, fn, cn, pn⟩)
    (M' := ⟨D, hn', fn', cn', pn'⟩) (hR := hR) ⟨rfl, hc, hf, hp⟩
  dsimp at ht hp ⊢
  induction A generalizing s with
  | predN P ts =>
    simp only [FormulaN.mapReduct, formulaEvalN, ht]
    have he : (fun i => termEval ⟨D, hn, fn, cn, pn⟩ s (ts (Fin.cast (hR.predArityCompat P) i))) =
        (hR.predArityCompat P ▸ (fun i => termEval ⟨D, hn, fn, cn, pn⟩ s (ts i))) := by
      exact cast_arity_args _ (fun i => termEval ⟨D, hn, fn, cn, pn⟩ s (ts i))
    rw [he]
    exact hp P _
  | eq_ he t u => simp only [FormulaN.mapReduct, formulaEvalN, ht]
  | neg A ih => exact not_congr (ih s)
  | conj A B ihA ihB => exact and_congr (ihA s) (ihB s)
  | disj A B ihA ihB => exact or_congr (ihA s) (ihB s)
  | impl A B ihA ihB => exact imp_congr (ihA s) (ihB s)
  | all x A ih => exact forall_congr' (fun a => ih (assignUpdate s x a))
  | ex x A ih => exact exists_congr (fun a => ih (assignUpdate s x a))

proof_of namingConst_freeForN := by
  induction A <;> simp_all [isFreeForN, namingConst, termFV]
  all_goals exact Or.inr (fun h => h)


helper /-- Lemma 5.4.4: For any structure M, assignment s, and type-c formula C
(in the extended language), M |= C[s] iff for every element a in M.carrier, M |= C(namingConst a)[s]. (Lemma 5.4.4 bundles type-c universal and type-d existential; this is the type-c primary.) -/
theorem typeC_satisfaction_iff {L : Language} (S : Structure L)
    (s : Assignment (extendedInterp S))
    (C : TypeC (extendedLanguage L S.carrier)) :
    SignedFormula.satisfiedBy (extendedInterp S) s (TypeC.toSigned C) ↔
    ∀ a : S.carrier,
      SignedFormula.satisfiedBy (extendedInterp S) s
        (TypeC.comp C (namingConst a) (namingConst_freeForN a C.var C.body)) :=
-- BEGIN PROOF
by
  have ncEval : ∀ (a : S.carrier) (s' : Assignment (extendedInterp S)),
      termEval (extendedInterp S) s' (namingConst a) = a :=
    fun a s' => namingConstEval S s' a
  cases C with
  | tAll x Y =>
    simp only [TypeC.toSigned, TypeC.comp, SignedFormula.satisfiedBy]
    constructor
    · intro h a
      exact (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mpr (h a)
    · intro h a
      exact (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mp (h a)
  | fEx x Y =>
    simp only [TypeC.toSigned, TypeC.comp, SignedFormula.satisfiedBy]
    constructor
    · intro h a habs
      exact h ⟨a, (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mp habs⟩
    · intro h ⟨a, ha⟩
      exact h a ((formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mpr ha)

helper /-- Lemma 5.4.4 (companion, Part ii): For any structure M, assignment
s, and type-d formula D (in the extended language), M |= D[s] iff for
at least one element a in M.carrier, M |= D(namingConst a)[s]. -/
theorem typeD_satisfaction_iff {L : Language} (S : Structure L)
    (s : Assignment (extendedInterp S))
    (D : TypeD (extendedLanguage L S.carrier)) :
    SignedFormula.satisfiedBy (extendedInterp S) s (TypeD.toSigned D) ↔
    ∃ a : S.carrier,
      SignedFormula.satisfiedBy (extendedInterp S) s
        (TypeD.comp D (namingConst a) (namingConst_freeForN a D.var D.body)) :=
-- BEGIN PROOF
by
  have ncEval : ∀ (a : S.carrier) (s' : Assignment (extendedInterp S)),
      termEval (extendedInterp S) s' (namingConst a) = a :=
    fun a s' => namingConstEval S s' a
  cases D with
  | tEx x Y =>
    simp only [TypeD.toSigned, TypeD.comp, SignedFormula.satisfiedBy]
    constructor
    · intro ⟨a, ha⟩
      exact ⟨a, (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mpr ha⟩
    · intro ⟨a, ha⟩
      exact ⟨a, (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).mp ha⟩
  | fAll x Y =>
    simp only [TypeD.toSigned, TypeD.comp, SignedFormula.satisfiedBy]
    have key : ∀ a : S.carrier,
        formulaEvalN (extendedInterp S) Y (assignUpdate s x a) ↔
        formulaEvalN (extendedInterp S) (formulaSubstN Y (namingConst a) x) s :=
      fun a => (formulaSubstEvalConstN _ Y _ x a (ncEval a) s).symm
    constructor
    · intro h
      have h' : ¬ ∀ a, formulaEvalN (extendedInterp S)
          (formulaSubstN Y (namingConst a) x) s :=
        fun hall => h (fun a => (key a).mpr (hall a))
      rw [Classical.not_forall] at h'
      obtain ⟨a, ha⟩ := h'
      exact ⟨a, ha⟩
    · intro ⟨a, ha⟩ hall
      exact ha ((key a).mp (hall a))

proof_of typeC_satisfaction_iffNoEq := typeC_satisfaction_iff S s C


proof_of typeD_satisfaction_iffNoEq := typeD_satisfaction_iff S s D


end LCS.FirstOrder.Gentzen.SignedFormulae
