import LCS.FirstOrder.Syntax.FreeGeneration.Terms

section

namespace LCS.FirstOrder.Syntax.FreeGeneration

open LCS.FirstOrder.Basic

open LCS.FirstOrder.Syntax

helper /-- Lemma 5.2.1 (companion): sum of termK values over a Fin-indexed
family of terms. -/
def termKSum {L : Language} {n : Nat} (ts : Fin n → Term L) : Int :=
  (List.ofFn (fun i => termK (ts i))).foldl (· + ·) 0

helper /-- Lemma 5.2.1 (companion): the sum of K values of n terms, each with K = 1,
equals n. Used in the inductive step of term_k_eq_one. -/
theorem termKSum_eq_arity {L : Language} {n : Nat}
    (ts : Fin n → Term L)
    (ih : ∀ i, termK (ts i) = 1) :
    termKSum ts = (n : Int) :=
-- BEGIN PROOF
by
  simp only [termKSum]
  -- We prove a general shifting lemma first
  have foldl_shift : ∀ (l : List Int) (init : Int),
      l.foldl (· + ·) init = init + l.foldl (· + ·) 0 := by
    intro l init
    induction l generalizing init with
    | nil => simp
    | cons b bs ihbs =>
      simp only [List.foldl_cons]
      rw [ihbs (init + b)]
      simp only [show (0 : Int) + b = b from by omega]
      rw [ihbs b]
      omega
  -- Now prove the main result by induction on n
  induction n with
  | zero => simp [List.ofFn]
  | succ n ihn =>
    rw [List.ofFn_succ, List.foldl_cons]
    rw [ih 0]
    rw [foldl_shift]
    rw [ihn (fun i => ts i.succ) (fun i => ih i.succ)]
    omega

proof_of term_k_eq_one := by
  -- BEGIN PROOF
    induction t with
    | var _ => rfl
    | const _ => rfl
    | func f ts ih =>
      simp only [termK]
      have := termKSum_eq_arity ts ih
      simp only [termKSum] at this
      rw [this]
      omega

helper /-- Flatten of ofFn of toSymbolList equals flatMap toSymbolList of ofFn. -/
theorem flatten_ofFn_eq_flatMap_ofFn {L : Language} {n : Nat}
    (ts : Fin n → Term L) :
    (List.ofFn (fun i => Term.toSymbolList (ts i))).flatten =
    (List.ofFn ts).flatMap Term.toSymbolList := by
-- BEGIN PROOF
  induction n with
  | zero => simp [List.ofFn]
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.ofFn_succ, List.flatMap_cons]
    congr 1; exact ih (fun i => ts i.succ)

helper /-- flatMap distributes over list append. -/
theorem flatMap_append_eq {α β : Type} (f : α → List β) (l1 l2 : List α) :
    (l1 ++ l2).flatMap f = l1.flatMap f ++ l2.flatMap f := by
-- BEGIN PROOF
  induction l1 with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih, List.append_assoc]

helper /-- A nonempty suffix of a flattened sequence of term symbol lists
decomposes as a flatMap of some nonempty list of terms. -/
theorem suffix_flatten_terms {L : Language} {n : Nat}
    (ts : Fin n → Term L)
    (ih : ∀ i, ∀ (suffix : List (TermSymbol L)),
      suffix <:+ Term.toSymbolList (ts i) → suffix ≠ [] →
      ∃ (terms : List (Term L)), terms ≠ [] ∧ suffix = terms.flatMap Term.toSymbolList)
    (suffix : List (TermSymbol L))
    (hSuffix : suffix <:+ (List.ofFn (fun i => Term.toSymbolList (ts i))).flatten)
    (hNe : suffix ≠ []) :
    ∃ (terms : List (Term L)), terms ≠ [] ∧ suffix = terms.flatMap Term.toSymbolList := by
-- BEGIN PROOF
  induction n with
  | zero => simp [List.ofFn] at hSuffix; exact absurd hSuffix hNe
  | succ m ihm =>
    rw [List.ofFn_succ, List.flatten_cons] at hSuffix
    obtain ⟨prefix_, hpfx⟩ := hSuffix
    by_cases hlen : prefix_.length < (Term.toSymbolList (ts 0)).length
    · obtain ⟨mid, hmid_t, hmid_s⟩ := list_split_left hpfx (by omega)
      have hm_ne : mid ≠ [] := by
        intro h; subst h; simp at hmid_t; rw [hmid_t] at hlen; simp at hlen
      obtain ⟨terms0, hne0, heq0⟩ := ih 0 mid ⟨prefix_, hmid_t.symm⟩ hm_ne
      rw [← hmid_s, heq0]
      refine ⟨terms0 ++ List.ofFn (fun i : Fin m => ts i.succ), ?_, ?_⟩
      · intro h; simp at h; exact hne0 h.1
      · rw [flatMap_append_eq]; congr 1
        exact (flatten_ofFn_eq_flatMap_ofFn (fun i : Fin m => ts i.succ))
    · obtain ⟨mid, _, hmid_s⟩ := list_split_left hpfx.symm (by omega)
      exact ihm (fun i => ts i.succ) (fun i => ih i.succ) ⟨mid, hmid_s⟩

proof_of term_suffix_is_term_concat := by
  -- BEGIN PROOF
    induction t generalizing suffix with
    | var n =>
      obtain ⟨pfx, hpfx⟩ := hSuffix
      simp [Term.toSymbolList] at hpfx
      have : suffix = [TermSymbol.varSym n] := by
        cases pfx with
        | nil => simpa using hpfx
        | cons a as =>
          simp at hpfx; obtain ⟨_, hrest⟩ := hpfx
          cases as with
          | nil => simp at hrest; exact absurd hrest hNe
          | cons b bs => simp at hrest
      subst this
      exact ⟨[Term.var n], by simp, by simp [Term.toSymbolList]⟩
    | const c =>
      obtain ⟨pfx, hpfx⟩ := hSuffix
      simp [Term.toSymbolList] at hpfx
      have : suffix = [TermSymbol.constSym c] := by
        cases pfx with
        | nil => simpa using hpfx
        | cons a as =>
          simp at hpfx; obtain ⟨_, hrest⟩ := hpfx
          cases as with
          | nil => simp at hrest; exact absurd hrest hNe
          | cons b bs => simp at hrest
      subst this
      exact ⟨[Term.const c], by simp, by simp [Term.toSymbolList]⟩
    | func f ts ih =>
      obtain ⟨pfx, hpfx⟩ := hSuffix
      simp only [Term.toSymbolList_func, List.singleton_append] at hpfx
      cases pfx with
      | nil =>
        simp at hpfx; rw [hpfx]
        exact ⟨[Term.func f ts], by simp, by simp⟩
      | cons x xs =>
        have hsuf : suffix <:+ (List.ofFn (fun i => Term.toSymbolList (ts i))).flatten := by
          have htl := List.tail_eq_of_cons_eq hpfx; simp at htl; exact ⟨xs, htl⟩
        exact suffix_flatten_terms ts ih suffix hsuf hNe

proof_of term_prefix_free := by
  -- BEGIN PROOF
    intro ⟨s, hs⟩
    have hk_w := termListK_toSymbolList s
    rw [hs] at hk_w
    have hk_le := term_prefix_k_le_zero t w rest hw hne
    omega

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

end LCS.FirstOrder.Syntax.FreeGeneration

end
