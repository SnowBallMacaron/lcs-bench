import LCS.Propositional.Syntax

namespace LCS.Propositional.Syntax

proof_of PropString.isFormula_closed := by
  refine ⟨(fun n => ⟨.var n, rfl⟩), ⟨.fls, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨a, rfl⟩
    exact ⟨.neg a, rfl⟩
  · rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨.conj a b, rfl⟩
  · rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨.disj a b, rfl⟩
  · rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨.impl a b, rfl⟩
  · rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨.equiv_ a b, rfl⟩


proof_of PropString.isFormula_least := by
  rintro s ⟨A, rfl⟩
  induction A with
  | var n => exact hvar n
  | fls => exact hfls
  | neg A ih => exact hneg A.toStr ih
  | conj A B ihA ihB => exact hconj A.toStr B.toStr ihA ihB
  | disj A B ihA ihB => exact hdisj A.toStr B.toStr ihA ihB
  | impl A B ihA ihB => exact himpl A.toStr B.toStr ihA ihB
  | equiv_ A B ihA ihB => exact hequiv A.toStr B.toStr ihA ihB


proof_of exSymbolsComputation_eq := by
  funext n
  apply propext
  simp only [exSymbolsComputation, PropFormula.symbols, Set.union]
  constructor
  · intro h
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  · intro h
    rcases h with h | h | h
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)


section Abbreviations

proof_of exPrecedence1 := rfl


proof_of exPrecedence2 := rfl


proof_of exLeftAssoc := rfl


end Abbreviations

helper theorem toStr_has_non_connNot (A : PropFormula) :
    ∃ c ∈ A.toStr, c ≠ PropAlphabet.connNot := by
-- BEGIN PROOF
  induction A with
  | var n =>
    refine ⟨.propSym n, ?_, nofun⟩
    simp [PropFormula.toStr]
  | fls =>
    refine ⟨.falsum, ?_, by decide⟩
    simp [PropFormula.toStr]
  | neg A ih =>
    obtain ⟨c, hc, hne⟩ := ih
    refine ⟨c, ?_, hne⟩
    simp [PropFormula.toStr, FormationFn.c_neg]
    right; exact hc
  | conj _ _ _ _ =>
    refine ⟨.lParen, ?_, by decide⟩
    simp [PropFormula.toStr, FormationFn.c_conj]
  | disj _ _ _ _ =>
    refine ⟨.lParen, ?_, by decide⟩
    simp [PropFormula.toStr, FormationFn.c_disj]
  | impl _ _ _ _ =>
    refine ⟨.lParen, ?_, by decide⟩
    simp [PropFormula.toStr, FormationFn.c_impl]
  | equiv_ _ _ _ _ =>
    refine ⟨.lParen, ?_, by decide⟩
    simp [PropFormula.toStr, FormationFn.c_equiv]

helper theorem toStr_ne_nil (A : PropFormula) : A.toStr ≠ [] := by
-- BEGIN PROOF
  cases A <;> simp [PropFormula.toStr, FormationFn.c_neg, FormationFn.c_conj,
    FormationFn.c_disj, FormationFn.c_impl, FormationFn.c_equiv]

helper theorem allConnNot_leftPC_zero (p : PropString) (h : ∀ c, c ∈ p → c = PropAlphabet.connNot) :
    PropString.leftParenCount p = 0 := by
  induction p with
  | nil => simp [PropString.leftParenCount, List.foldl]
  | cons hd tl ih =>
    have hhd := h hd (by simp); subst hhd
    rw [show (PropAlphabet.connNot :: tl : PropString) = [PropAlphabet.connNot] ++ tl from rfl]
    rw [leftParenCount_append]
    have : PropString.leftParenCount [PropAlphabet.connNot] = 0 := by decide
    have := ih (fun c hc => h c (by simp [hc])); omega

helper theorem allConnNot_rightPC_zero (p : PropString) (h : ∀ c, c ∈ p → c = PropAlphabet.connNot) :
    PropString.rightParenCount p = 0 := by
  induction p with
  | nil => simp [PropString.rightParenCount, List.foldl]
  | cons hd tl ih =>
    have hhd := h hd (by simp); subst hhd
    rw [show (PropAlphabet.connNot :: tl : PropString) = [PropAlphabet.connNot] ++ tl from rfl]
    rw [rightParenCount_append]
    have : PropString.rightParenCount [PropAlphabet.connNot] = 0 := by decide
    have := ih (fun c hc => h c (by simp [hc])); omega

helper theorem prefix_balance_conj (A B : PropFormula)
    (ihA : ∀ q : PropString, q <+: A.toStr → q.leftParenCount ≥ q.rightParenCount)
    (ihB : ∀ q : PropString, q <+: B.toStr → q.leftParenCount ≥ q.rightParenCount)
    (q : PropString) (hq : q <+: (PropFormula.conj A B).toStr) :
    q.leftParenCount ≥ q.rightParenCount := by
  obtain ⟨s, hs⟩ := hq
  simp only [PropFormula.toStr, FormationFn.c_conj] at hs
  rw [List.append_assoc, List.append_assoc, List.append_assoc] at hs
  cases q with
  | nil =>
    have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
    have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
    omega
  | cons h t =>
    have hh := List.head_eq_of_cons_eq hs
    have ht : t ++ s = A.toStr ++ ([.connAnd] ++ (B.toStr ++ [.rParen])) := by
      have := List.tail_eq_of_cons_eq hs; simpa using this
    subst hh
    rw [show (PropAlphabet.lParen :: t : PropString) = [PropAlphabet.lParen] ++ t from rfl]
    rw [leftParenCount_append, rightParenCount_append]
    have hlp : PropString.leftParenCount [PropAlphabet.lParen] = 1 := by decide
    have hrp : PropString.rightParenCount [PropAlphabet.lParen] = 0 := by decide
    rw [hlp, hrp]
    -- Goal: 1 + leftPC(t) ≥ 0 + rightPC(t). Suffices leftPC(t)+1 ≥ rightPC(t).
    suffices hsuff : PropString.leftParenCount t + 1 ≥ PropString.rightParenCount t by omega
    by_cases hlen1 : t.length ≤ A.toStr.length
    · have := ihA t (prefix_of_append_eq ht hlen1); omega
    · obtain ⟨rest1, hrest1, hrest1s⟩ := split_past_prefix ht (by omega)
      rw [hrest1, leftParenCount_append, rightParenCount_append]
      have hbal := propFormula_balanced_parens A
      by_cases hlen2 : rest1.length ≤ ([PropAlphabet.connAnd] : PropString).length
      · cases rest1 with
        | nil =>
          have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
          have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
          omega
        | cons c1 t1 =>
          have : t1 = [] := by
            have : (c1 :: t1).length ≤ 1 := hlen2; simp at this
            cases t1 with | nil => rfl | cons _ _ => simp at this
          subst this
          have hpre1 := prefix_of_append_eq hrest1s hlen2
          have : c1 = PropAlphabet.connAnd := by
            obtain ⟨w, hw⟩ := hpre1; simp at hw; exact hw.1
          subst this
          have h1 : PropString.leftParenCount [PropAlphabet.connAnd] = 0 := by decide
          have h2 : PropString.rightParenCount [PropAlphabet.connAnd] = 0 := by decide
          omega
      · obtain ⟨rest2, hrest2, hrest2s⟩ := split_past_prefix hrest1s (by omega)
        rw [hrest2, leftParenCount_append, rightParenCount_append]
        have h1 : PropString.leftParenCount [PropAlphabet.connAnd] = 0 := by decide
        have h2 : PropString.rightParenCount [PropAlphabet.connAnd] = 0 := by decide
        by_cases hlen3 : rest2.length ≤ B.toStr.length
        · have := ihB rest2 (prefix_of_append_eq hrest2s hlen3); omega
        · obtain ⟨rest3, hrest3, hrest3s⟩ := split_past_prefix hrest2s (by omega)
          rw [hrest3, leftParenCount_append, rightParenCount_append]
          have hbalB := propFormula_balanced_parens B
          cases rest3 with
          | nil =>
            have h3 : PropString.leftParenCount ([] : PropString) = 0 := by decide
            have h4 : PropString.rightParenCount ([] : PropString) = 0 := by decide
            omega
          | cons c3 t3 =>
            have ht3s : t3 ++ s = [] := by
              have := List.tail_eq_of_cons_eq hrest3s; simpa using this
            have : t3 = [] := by cases t3 with | nil => rfl | cons _ _ => simp at ht3s
            subst this; simp at hrest3s
            obtain ⟨hc3, _⟩ := hrest3s; subst hc3
            have h3 : PropString.leftParenCount [PropAlphabet.rParen] = 0 := by decide
            have h4 : PropString.rightParenCount [PropAlphabet.rParen] = 1 := by decide
            omega

helper theorem prefix_balance_disj (A B : PropFormula)
    (ihA : ∀ q : PropString, q <+: A.toStr → q.leftParenCount ≥ q.rightParenCount)
    (ihB : ∀ q : PropString, q <+: B.toStr → q.leftParenCount ≥ q.rightParenCount)
    (q : PropString) (hq : q <+: (PropFormula.disj A B).toStr) :
    q.leftParenCount ≥ q.rightParenCount := by
  obtain ⟨s, hs⟩ := hq
  simp only [PropFormula.toStr, FormationFn.c_disj] at hs
  rw [List.append_assoc, List.append_assoc, List.append_assoc] at hs
  cases q with
  | nil =>
    have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
    have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
    omega
  | cons h t =>
    have hh := List.head_eq_of_cons_eq hs
    have ht : t ++ s = A.toStr ++ ([.connOr] ++ (B.toStr ++ [.rParen])) := by
      have := List.tail_eq_of_cons_eq hs; simpa using this
    subst hh
    rw [show (PropAlphabet.lParen :: t : PropString) = [PropAlphabet.lParen] ++ t from rfl]
    rw [leftParenCount_append, rightParenCount_append]
    have hlp : PropString.leftParenCount [PropAlphabet.lParen] = 1 := by decide
    have hrp : PropString.rightParenCount [PropAlphabet.lParen] = 0 := by decide
    rw [hlp, hrp]
    suffices hsuff : PropString.leftParenCount t + 1 ≥ PropString.rightParenCount t by omega
    by_cases hlen1 : t.length ≤ A.toStr.length
    · have := ihA t (prefix_of_append_eq ht hlen1); omega
    · obtain ⟨rest1, hrest1, hrest1s⟩ := split_past_prefix ht (by omega)
      rw [hrest1, leftParenCount_append, rightParenCount_append]
      have hbal := propFormula_balanced_parens A
      by_cases hlen2 : rest1.length ≤ ([PropAlphabet.connOr] : PropString).length
      · cases rest1 with
        | nil =>
          have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
          have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
          omega
        | cons c1 t1 =>
          have : t1 = [] := by
            have : (c1 :: t1).length ≤ 1 := hlen2; simp at this
            cases t1 with | nil => rfl | cons _ _ => simp at this
          subst this
          have : c1 = PropAlphabet.connOr := by
            obtain ⟨w, hw⟩ := prefix_of_append_eq hrest1s hlen2; simp at hw; exact hw.1
          subst this
          have h1 : PropString.leftParenCount [PropAlphabet.connOr] = 0 := by decide
          have h2 : PropString.rightParenCount [PropAlphabet.connOr] = 0 := by decide
          omega
      · obtain ⟨rest2, hrest2, hrest2s⟩ := split_past_prefix hrest1s (by omega)
        rw [hrest2, leftParenCount_append, rightParenCount_append]
        have h1 : PropString.leftParenCount [PropAlphabet.connOr] = 0 := by decide
        have h2 : PropString.rightParenCount [PropAlphabet.connOr] = 0 := by decide
        by_cases hlen3 : rest2.length ≤ B.toStr.length
        · have := ihB rest2 (prefix_of_append_eq hrest2s hlen3); omega
        · obtain ⟨rest3, hrest3, hrest3s⟩ := split_past_prefix hrest2s (by omega)
          rw [hrest3, leftParenCount_append, rightParenCount_append]
          have hbalB := propFormula_balanced_parens B
          cases rest3 with
          | nil =>
            have h3 : PropString.leftParenCount ([] : PropString) = 0 := by decide
            have h4 : PropString.rightParenCount ([] : PropString) = 0 := by decide
            omega
          | cons c3 t3 =>
            have ht3s : t3 ++ s = [] := by
              have := List.tail_eq_of_cons_eq hrest3s; simpa using this
            have : t3 = [] := by cases t3 with | nil => rfl | cons _ _ => simp at ht3s
            subst this; simp at hrest3s
            obtain ⟨hc3, _⟩ := hrest3s; subst hc3
            have h3 : PropString.leftParenCount [PropAlphabet.rParen] = 0 := by decide
            have h4 : PropString.rightParenCount [PropAlphabet.rParen] = 1 := by decide
            omega

helper theorem prefix_balance_impl (A B : PropFormula)
    (ihA : ∀ q : PropString, q <+: A.toStr → q.leftParenCount ≥ q.rightParenCount)
    (ihB : ∀ q : PropString, q <+: B.toStr → q.leftParenCount ≥ q.rightParenCount)
    (q : PropString) (hq : q <+: (PropFormula.impl A B).toStr) :
    q.leftParenCount ≥ q.rightParenCount := by
  obtain ⟨s, hs⟩ := hq
  simp only [PropFormula.toStr, FormationFn.c_impl] at hs
  rw [List.append_assoc, List.append_assoc, List.append_assoc] at hs
  cases q with
  | nil =>
    have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
    have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
    omega
  | cons h t =>
    have hh := List.head_eq_of_cons_eq hs
    have ht : t ++ s = A.toStr ++ ([.connImpl] ++ (B.toStr ++ [.rParen])) := by
      have := List.tail_eq_of_cons_eq hs; simpa using this
    subst hh
    rw [show (PropAlphabet.lParen :: t : PropString) = [PropAlphabet.lParen] ++ t from rfl]
    rw [leftParenCount_append, rightParenCount_append]
    have hlp : PropString.leftParenCount [PropAlphabet.lParen] = 1 := by decide
    have hrp : PropString.rightParenCount [PropAlphabet.lParen] = 0 := by decide
    rw [hlp, hrp]
    suffices hsuff : PropString.leftParenCount t + 1 ≥ PropString.rightParenCount t by omega
    by_cases hlen1 : t.length ≤ A.toStr.length
    · have := ihA t (prefix_of_append_eq ht hlen1); omega
    · obtain ⟨rest1, hrest1, hrest1s⟩ := split_past_prefix ht (by omega)
      rw [hrest1, leftParenCount_append, rightParenCount_append]
      have hbal := propFormula_balanced_parens A
      by_cases hlen2 : rest1.length ≤ ([PropAlphabet.connImpl] : PropString).length
      · cases rest1 with
        | nil =>
          have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
          have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
          omega
        | cons c1 t1 =>
          have : t1 = [] := by
            have : (c1 :: t1).length ≤ 1 := hlen2; simp at this
            cases t1 with | nil => rfl | cons _ _ => simp at this
          subst this
          have : c1 = PropAlphabet.connImpl := by
            obtain ⟨w, hw⟩ := prefix_of_append_eq hrest1s hlen2; simp at hw; exact hw.1
          subst this
          have h1 : PropString.leftParenCount [PropAlphabet.connImpl] = 0 := by decide
          have h2 : PropString.rightParenCount [PropAlphabet.connImpl] = 0 := by decide
          omega
      · obtain ⟨rest2, hrest2, hrest2s⟩ := split_past_prefix hrest1s (by omega)
        rw [hrest2, leftParenCount_append, rightParenCount_append]
        have h1 : PropString.leftParenCount [PropAlphabet.connImpl] = 0 := by decide
        have h2 : PropString.rightParenCount [PropAlphabet.connImpl] = 0 := by decide
        by_cases hlen3 : rest2.length ≤ B.toStr.length
        · have := ihB rest2 (prefix_of_append_eq hrest2s hlen3); omega
        · obtain ⟨rest3, hrest3, hrest3s⟩ := split_past_prefix hrest2s (by omega)
          rw [hrest3, leftParenCount_append, rightParenCount_append]
          have hbalB := propFormula_balanced_parens B
          cases rest3 with
          | nil =>
            have h3 : PropString.leftParenCount ([] : PropString) = 0 := by decide
            have h4 : PropString.rightParenCount ([] : PropString) = 0 := by decide
            omega
          | cons c3 t3 =>
            have ht3s : t3 ++ s = [] := by
              have := List.tail_eq_of_cons_eq hrest3s; simpa using this
            have : t3 = [] := by cases t3 with | nil => rfl | cons _ _ => simp at ht3s
            subst this; simp at hrest3s
            obtain ⟨hc3, _⟩ := hrest3s; subst hc3
            have h3 : PropString.leftParenCount [PropAlphabet.rParen] = 0 := by decide
            have h4 : PropString.rightParenCount [PropAlphabet.rParen] = 1 := by decide
            omega

helper theorem prefix_balance_equiv_ (A B : PropFormula)
    (ihA : ∀ q : PropString, q <+: A.toStr → q.leftParenCount ≥ q.rightParenCount)
    (ihB : ∀ q : PropString, q <+: B.toStr → q.leftParenCount ≥ q.rightParenCount)
    (q : PropString) (hq : q <+: (PropFormula.equiv_ A B).toStr) :
    q.leftParenCount ≥ q.rightParenCount := by
  obtain ⟨s, hs⟩ := hq
  simp only [PropFormula.toStr, FormationFn.c_equiv] at hs
  rw [List.append_assoc, List.append_assoc, List.append_assoc] at hs
  cases q with
  | nil =>
    have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
    have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
    omega
  | cons h t =>
    have hh := List.head_eq_of_cons_eq hs
    have ht : t ++ s = A.toStr ++ ([.connEquiv] ++ (B.toStr ++ [.rParen])) := by
      have := List.tail_eq_of_cons_eq hs; simpa using this
    subst hh
    rw [show (PropAlphabet.lParen :: t : PropString) = [PropAlphabet.lParen] ++ t from rfl]
    rw [leftParenCount_append, rightParenCount_append]
    have hlp : PropString.leftParenCount [PropAlphabet.lParen] = 1 := by decide
    have hrp : PropString.rightParenCount [PropAlphabet.lParen] = 0 := by decide
    rw [hlp, hrp]
    suffices hsuff : PropString.leftParenCount t + 1 ≥ PropString.rightParenCount t by omega
    by_cases hlen1 : t.length ≤ A.toStr.length
    · have := ihA t (prefix_of_append_eq ht hlen1); omega
    · obtain ⟨rest1, hrest1, hrest1s⟩ := split_past_prefix ht (by omega)
      rw [hrest1, leftParenCount_append, rightParenCount_append]
      have hbal := propFormula_balanced_parens A
      by_cases hlen2 : rest1.length ≤ ([PropAlphabet.connEquiv] : PropString).length
      · cases rest1 with
        | nil =>
          have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
          have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
          omega
        | cons c1 t1 =>
          have : t1 = [] := by
            have : (c1 :: t1).length ≤ 1 := hlen2; simp at this
            cases t1 with | nil => rfl | cons _ _ => simp at this
          subst this
          have : c1 = PropAlphabet.connEquiv := by
            obtain ⟨w, hw⟩ := prefix_of_append_eq hrest1s hlen2; simp at hw; exact hw.1
          subst this
          have h1 : PropString.leftParenCount [PropAlphabet.connEquiv] = 0 := by decide
          have h2 : PropString.rightParenCount [PropAlphabet.connEquiv] = 0 := by decide
          omega
      · obtain ⟨rest2, hrest2, hrest2s⟩ := split_past_prefix hrest1s (by omega)
        rw [hrest2, leftParenCount_append, rightParenCount_append]
        have h1 : PropString.leftParenCount [PropAlphabet.connEquiv] = 0 := by decide
        have h2 : PropString.rightParenCount [PropAlphabet.connEquiv] = 0 := by decide
        by_cases hlen3 : rest2.length ≤ B.toStr.length
        · have := ihB rest2 (prefix_of_append_eq hrest2s hlen3); omega
        · obtain ⟨rest3, hrest3, hrest3s⟩ := split_past_prefix hrest2s (by omega)
          rw [hrest3, leftParenCount_append, rightParenCount_append]
          have hbalB := propFormula_balanced_parens B
          cases rest3 with
          | nil =>
            have h3 : PropString.leftParenCount ([] : PropString) = 0 := by decide
            have h4 : PropString.rightParenCount ([] : PropString) = 0 := by decide
            omega
          | cons c3 t3 =>
            have ht3s : t3 ++ s = [] := by
              have := List.tail_eq_of_cons_eq hrest3s; simpa using this
            have : t3 = [] := by cases t3 with | nil => rfl | cons _ _ => simp at ht3s
            subst this; simp at hrest3s
            obtain ⟨hc3, _⟩ := hrest3s; subst hc3
            have h3 : PropString.leftParenCount [PropAlphabet.rParen] = 0 := by decide
            have h4 : PropString.rightParenCount [PropAlphabet.rParen] = 1 := by decide
            omega

helper theorem toStr_prefix_lpc_ge_rpc (A : PropFormula) (q : PropString)
    (hq : q <+: A.toStr) :
    q.leftParenCount ≥ q.rightParenCount := by
-- BEGIN PROOF
  induction A generalizing q with
  | var n =>
    obtain ⟨s, hs⟩ := hq
    simp [PropFormula.toStr] at hs
    cases q with
    | nil =>
      have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
      have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
      omega
    | cons h t =>
      have hh := List.head_eq_of_cons_eq hs
      have ht : t ++ s = [] := by have := List.tail_eq_of_cons_eq hs; simpa using this
      have : t = [] := by cases t with | nil => rfl | cons _ _ => simp at ht
      subst this; simp at ht; subst ht; subst hh
      have h1 : PropString.leftParenCount [PropAlphabet.propSym n] = 0 := by
        simp [PropString.leftParenCount, List.foldl]
      have h2 : PropString.rightParenCount [PropAlphabet.propSym n] = 0 := by
        simp [PropString.rightParenCount, List.foldl]
      omega
  | fls =>
    obtain ⟨s, hs⟩ := hq
    simp [PropFormula.toStr] at hs
    cases q with
    | nil =>
      have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
      have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
      omega
    | cons h t =>
      have hh := List.head_eq_of_cons_eq hs
      have ht : t ++ s = [] := by have := List.tail_eq_of_cons_eq hs; simpa using this
      have : t = [] := by cases t with | nil => rfl | cons _ _ => simp at ht
      subst this; simp at ht; subst ht; subst hh
      have h1 : PropString.leftParenCount [PropAlphabet.falsum] = 0 := by decide
      have h2 : PropString.rightParenCount [PropAlphabet.falsum] = 0 := by decide
      omega
  | neg A ih =>
    obtain ⟨s, hs⟩ := hq
    simp [PropFormula.toStr, FormationFn.c_neg] at hs
    cases q with
    | nil =>
      have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
      have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
      omega
    | cons h t =>
      have hh := List.head_eq_of_cons_eq hs
      have ht : t ++ s = A.toStr := by have := List.tail_eq_of_cons_eq hs; simpa using this
      subst hh
      have := ih t ⟨s, ht⟩
      rw [show (PropAlphabet.connNot :: t : PropString) = [PropAlphabet.connNot] ++ t from rfl]
      rw [leftParenCount_append, rightParenCount_append]
      have h1 : PropString.leftParenCount [PropAlphabet.connNot] = 0 := by decide
      have h2 : PropString.rightParenCount [PropAlphabet.connNot] = 0 := by decide
      omega
  | conj A B ihA ihB => exact prefix_balance_conj A B ihA ihB q hq
  | disj A B ihA ihB => exact prefix_balance_disj A B ihA ihB q hq
  | impl A B ihA ihB => exact prefix_balance_impl A B ihA ihB q hq
  | equiv_ A B ihA ihB => exact prefix_balance_equiv_ A B ihA ihB q hq

helper theorem proper_prefix_conj (A B : PropFormula) (p : PropString)
    (hpre : p <+: (PropFormula.conj A B).toStr)
    (hne : p ≠ (PropFormula.conj A B).toStr) :
    p = [] ∨ (∀ c, c ∈ p → c = PropAlphabet.connNot) ∨
    p.leftParenCount > p.rightParenCount := by
  -- p is a proper prefix of [lParen] ++ A.toStr ++ [connAnd] ++ B.toStr ++ [rParen]
  -- If p = [], done. Otherwise p starts with lParen, so leftPC(p) ≥ 1.
  -- Since p is proper, it's missing at least the final rParen.
  -- By toStr_prefix_lpc_ge_rpc on A (for sub-prefixes within A.toStr),
  -- we can show leftPC(p) > rightPC(p).
  obtain ⟨suffix, hsuffix⟩ := hpre
  simp only [PropFormula.toStr, FormationFn.c_conj] at hsuffix hne
  cases p with
  | nil => left; rfl
  | cons ph pt =>
    right; right
    rw [List.append_assoc, List.append_assoc, List.append_assoc] at hsuffix
    have hph := List.head_eq_of_cons_eq hsuffix
    have ht : pt ++ suffix = A.toStr ++ ([.connAnd] ++ (B.toStr ++ [.rParen])) := by
      have := List.tail_eq_of_cons_eq hsuffix; simpa using this
    subst hph
    rw [show (PropAlphabet.lParen :: pt : PropString) = [PropAlphabet.lParen] ++ pt from rfl]
    rw [leftParenCount_append, rightParenCount_append]
    have hlp : PropString.leftParenCount [PropAlphabet.lParen] = 1 := by decide
    have hrp : PropString.rightParenCount [PropAlphabet.lParen] = 0 := by decide
    rw [hlp, hrp]
    -- Goal: 1 + leftPC(pt) > 0 + rightPC(pt). Need leftPC(pt) ≥ rightPC(pt).
    -- pt is a PROPER prefix of A.toStr ++ [connAnd] ++ B.toStr ++ [rParen]
    -- (proper because suffix ≠ [])
    have hsuffix_ne : suffix ≠ [] := by
      intro heq; subst heq; simp at hsuffix hne; exact hne hsuffix
    suffices hsuff : PropString.leftParenCount pt ≥ PropString.rightParenCount pt by omega
    by_cases hlen1 : pt.length ≤ A.toStr.length
    · exact toStr_prefix_lpc_ge_rpc A pt (prefix_of_append_eq ht hlen1)
    · obtain ⟨rest1, hrest1, hrest1s⟩ := split_past_prefix ht (by omega)
      rw [hrest1, leftParenCount_append, rightParenCount_append]
      have hbal := propFormula_balanced_parens A
      by_cases hlen2 : rest1.length ≤ ([PropAlphabet.connAnd] : PropString).length
      · cases rest1 with
        | nil =>
          have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
          have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
          omega
        | cons c1 t1 =>
          have : t1 = [] := by
            have : (c1 :: t1).length ≤ 1 := hlen2; simp at this
            cases t1 with | nil => rfl | cons _ _ => simp at this
          subst this
          have : c1 = PropAlphabet.connAnd := by
            obtain ⟨w, hw⟩ := prefix_of_append_eq hrest1s hlen2; simp at hw; exact hw.1
          subst this
          have h1 : PropString.leftParenCount [PropAlphabet.connAnd] = 0 := by decide
          have h2 : PropString.rightParenCount [PropAlphabet.connAnd] = 0 := by decide
          omega
      · obtain ⟨rest2, hrest2, hrest2s⟩ := split_past_prefix hrest1s (by omega)
        rw [hrest2, leftParenCount_append, rightParenCount_append]
        have h1 : PropString.leftParenCount [PropAlphabet.connAnd] = 0 := by decide
        have h2 : PropString.rightParenCount [PropAlphabet.connAnd] = 0 := by decide
        by_cases hlen3 : rest2.length ≤ B.toStr.length
        · have := toStr_prefix_lpc_ge_rpc B rest2 (prefix_of_append_eq hrest2s hlen3); omega
        · -- rest2 extends past B.toStr, so rest2 = B.toStr ++ rest3 with rest3 <+: [rParen]
          obtain ⟨rest3, hrest3, hrest3s⟩ := split_past_prefix hrest2s (by omega)
          rw [hrest3, leftParenCount_append, rightParenCount_append]
          have hbalB := propFormula_balanced_parens B
          -- rest3 is a prefix of [rParen]. Since suffix ≠ [], rest3 must be [].
          cases rest3 with
          | nil =>
            have h3 : PropString.leftParenCount ([] : PropString) = 0 := by decide
            have h4 : PropString.rightParenCount ([] : PropString) = 0 := by decide
            omega
          | cons c3 t3 =>
            -- rest3 = [rParen], meaning pt = full inner string, contradiction
            have ht3s : t3 ++ suffix = [] := by
              have := List.tail_eq_of_cons_eq hrest3s; simpa using this
            have : t3 = [] := by cases t3 with | nil => rfl | cons _ _ => simp at ht3s
            subst this
            have : suffix = [] := by simpa using ht3s
            exact absurd this hsuffix_ne

helper theorem proper_prefix_disj (A B : PropFormula) (p : PropString)
    (hpre : p <+: (PropFormula.disj A B).toStr)
    (hne : p ≠ (PropFormula.disj A B).toStr) :
    p = [] ∨ (∀ c, c ∈ p → c = PropAlphabet.connNot) ∨
    p.leftParenCount > p.rightParenCount := by
  obtain ⟨suffix, hsuffix⟩ := hpre
  simp only [PropFormula.toStr, FormationFn.c_disj] at hsuffix hne
  cases p with
  | nil => left; rfl
  | cons ph pt =>
    right; right
    rw [List.append_assoc, List.append_assoc, List.append_assoc] at hsuffix
    have hph := List.head_eq_of_cons_eq hsuffix
    have ht : pt ++ suffix = A.toStr ++ ([.connOr] ++ (B.toStr ++ [.rParen])) := by
      have := List.tail_eq_of_cons_eq hsuffix; simpa using this
    subst hph
    rw [show (PropAlphabet.lParen :: pt : PropString) = [PropAlphabet.lParen] ++ pt from rfl]
    rw [leftParenCount_append, rightParenCount_append]
    have hlp : PropString.leftParenCount [PropAlphabet.lParen] = 1 := by decide
    have hrp : PropString.rightParenCount [PropAlphabet.lParen] = 0 := by decide
    rw [hlp, hrp]
    have hsuffix_ne : suffix ≠ [] := by
      intro heq; subst heq; simp at hsuffix hne; exact hne hsuffix
    suffices hsuff : PropString.leftParenCount pt ≥ PropString.rightParenCount pt by omega
    by_cases hlen1 : pt.length ≤ A.toStr.length
    · exact toStr_prefix_lpc_ge_rpc A pt (prefix_of_append_eq ht hlen1)
    · obtain ⟨rest1, hrest1, hrest1s⟩ := split_past_prefix ht (by omega)
      rw [hrest1, leftParenCount_append, rightParenCount_append]
      have hbal := propFormula_balanced_parens A
      by_cases hlen2 : rest1.length ≤ ([PropAlphabet.connOr] : PropString).length
      · cases rest1 with
        | nil =>
          have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
          have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
          omega
        | cons c1 t1 =>
          have : t1 = [] := by
            have : (c1 :: t1).length ≤ 1 := hlen2; simp at this
            cases t1 with | nil => rfl | cons _ _ => simp at this
          subst this
          have : c1 = PropAlphabet.connOr := by
            obtain ⟨w, hw⟩ := prefix_of_append_eq hrest1s hlen2; simp at hw; exact hw.1
          subst this
          have h1 : PropString.leftParenCount [PropAlphabet.connOr] = 0 := by decide
          have h2 : PropString.rightParenCount [PropAlphabet.connOr] = 0 := by decide
          omega
      · obtain ⟨rest2, hrest2, hrest2s⟩ := split_past_prefix hrest1s (by omega)
        rw [hrest2, leftParenCount_append, rightParenCount_append]
        have h1 : PropString.leftParenCount [PropAlphabet.connOr] = 0 := by decide
        have h2 : PropString.rightParenCount [PropAlphabet.connOr] = 0 := by decide
        by_cases hlen3 : rest2.length ≤ B.toStr.length
        · have := toStr_prefix_lpc_ge_rpc B rest2 (prefix_of_append_eq hrest2s hlen3); omega
        · obtain ⟨rest3, hrest3, hrest3s⟩ := split_past_prefix hrest2s (by omega)
          cases rest3 with
          | nil =>
            rw [hrest3, leftParenCount_append, rightParenCount_append]
            have hbalB := propFormula_balanced_parens B
            have h3 : PropString.leftParenCount ([] : PropString) = 0 := by decide
            have h4 : PropString.rightParenCount ([] : PropString) = 0 := by decide
            omega
          | cons c3 t3 =>
            have ht3s : t3 ++ suffix = [] := by
              have := List.tail_eq_of_cons_eq hrest3s; simpa using this
            have : t3 = [] := by cases t3 with | nil => rfl | cons _ _ => simp at ht3s
            subst this
            have : suffix = [] := by simpa using ht3s
            exact absurd this hsuffix_ne

helper theorem proper_prefix_impl (A B : PropFormula) (p : PropString)
    (hpre : p <+: (PropFormula.impl A B).toStr)
    (hne : p ≠ (PropFormula.impl A B).toStr) :
    p = [] ∨ (∀ c, c ∈ p → c = PropAlphabet.connNot) ∨
    p.leftParenCount > p.rightParenCount := by
  obtain ⟨suffix, hsuffix⟩ := hpre
  simp only [PropFormula.toStr, FormationFn.c_impl] at hsuffix hne
  cases p with
  | nil => left; rfl
  | cons ph pt =>
    right; right
    rw [List.append_assoc, List.append_assoc, List.append_assoc] at hsuffix
    have hph := List.head_eq_of_cons_eq hsuffix
    have ht : pt ++ suffix = A.toStr ++ ([.connImpl] ++ (B.toStr ++ [.rParen])) := by
      have := List.tail_eq_of_cons_eq hsuffix; simpa using this
    subst hph
    rw [show (PropAlphabet.lParen :: pt : PropString) = [PropAlphabet.lParen] ++ pt from rfl]
    rw [leftParenCount_append, rightParenCount_append]
    have hlp : PropString.leftParenCount [PropAlphabet.lParen] = 1 := by decide
    have hrp : PropString.rightParenCount [PropAlphabet.lParen] = 0 := by decide
    rw [hlp, hrp]
    have hsuffix_ne : suffix ≠ [] := by
      intro heq; subst heq; simp at hsuffix hne; exact hne hsuffix
    suffices hsuff : PropString.leftParenCount pt ≥ PropString.rightParenCount pt by omega
    by_cases hlen1 : pt.length ≤ A.toStr.length
    · exact toStr_prefix_lpc_ge_rpc A pt (prefix_of_append_eq ht hlen1)
    · obtain ⟨rest1, hrest1, hrest1s⟩ := split_past_prefix ht (by omega)
      rw [hrest1, leftParenCount_append, rightParenCount_append]
      have hbal := propFormula_balanced_parens A
      by_cases hlen2 : rest1.length ≤ ([PropAlphabet.connImpl] : PropString).length
      · cases rest1 with
        | nil =>
          have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
          have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
          omega
        | cons c1 t1 =>
          have : t1 = [] := by
            have : (c1 :: t1).length ≤ 1 := hlen2; simp at this
            cases t1 with | nil => rfl | cons _ _ => simp at this
          subst this
          have : c1 = PropAlphabet.connImpl := by
            obtain ⟨w, hw⟩ := prefix_of_append_eq hrest1s hlen2; simp at hw; exact hw.1
          subst this
          have h1 : PropString.leftParenCount [PropAlphabet.connImpl] = 0 := by decide
          have h2 : PropString.rightParenCount [PropAlphabet.connImpl] = 0 := by decide
          omega
      · obtain ⟨rest2, hrest2, hrest2s⟩ := split_past_prefix hrest1s (by omega)
        rw [hrest2, leftParenCount_append, rightParenCount_append]
        have h1 : PropString.leftParenCount [PropAlphabet.connImpl] = 0 := by decide
        have h2 : PropString.rightParenCount [PropAlphabet.connImpl] = 0 := by decide
        by_cases hlen3 : rest2.length ≤ B.toStr.length
        · have := toStr_prefix_lpc_ge_rpc B rest2 (prefix_of_append_eq hrest2s hlen3); omega
        · obtain ⟨rest3, hrest3, hrest3s⟩ := split_past_prefix hrest2s (by omega)
          cases rest3 with
          | nil =>
            rw [hrest3, leftParenCount_append, rightParenCount_append]
            have hbalB := propFormula_balanced_parens B
            have h3 : PropString.leftParenCount ([] : PropString) = 0 := by decide
            have h4 : PropString.rightParenCount ([] : PropString) = 0 := by decide
            omega
          | cons c3 t3 =>
            have ht3s : t3 ++ suffix = [] := by
              have := List.tail_eq_of_cons_eq hrest3s; simpa using this
            have : t3 = [] := by cases t3 with | nil => rfl | cons _ _ => simp at ht3s
            subst this
            have : suffix = [] := by simpa using ht3s
            exact absurd this hsuffix_ne

helper theorem proper_prefix_equiv_ (A B : PropFormula) (p : PropString)
    (hpre : p <+: (PropFormula.equiv_ A B).toStr)
    (hne : p ≠ (PropFormula.equiv_ A B).toStr) :
    p = [] ∨ (∀ c, c ∈ p → c = PropAlphabet.connNot) ∨
    p.leftParenCount > p.rightParenCount := by
  obtain ⟨suffix, hsuffix⟩ := hpre
  simp only [PropFormula.toStr, FormationFn.c_equiv] at hsuffix hne
  cases p with
  | nil => left; rfl
  | cons ph pt =>
    right; right
    rw [List.append_assoc, List.append_assoc, List.append_assoc] at hsuffix
    have hph := List.head_eq_of_cons_eq hsuffix
    have ht : pt ++ suffix = A.toStr ++ ([.connEquiv] ++ (B.toStr ++ [.rParen])) := by
      have := List.tail_eq_of_cons_eq hsuffix; simpa using this
    subst hph
    rw [show (PropAlphabet.lParen :: pt : PropString) = [PropAlphabet.lParen] ++ pt from rfl]
    rw [leftParenCount_append, rightParenCount_append]
    have hlp : PropString.leftParenCount [PropAlphabet.lParen] = 1 := by decide
    have hrp : PropString.rightParenCount [PropAlphabet.lParen] = 0 := by decide
    rw [hlp, hrp]
    have hsuffix_ne : suffix ≠ [] := by
      intro heq; subst heq; simp at hsuffix hne; exact hne hsuffix
    suffices hsuff : PropString.leftParenCount pt ≥ PropString.rightParenCount pt by omega
    by_cases hlen1 : pt.length ≤ A.toStr.length
    · exact toStr_prefix_lpc_ge_rpc A pt (prefix_of_append_eq ht hlen1)
    · obtain ⟨rest1, hrest1, hrest1s⟩ := split_past_prefix ht (by omega)
      rw [hrest1, leftParenCount_append, rightParenCount_append]
      have hbal := propFormula_balanced_parens A
      by_cases hlen2 : rest1.length ≤ ([PropAlphabet.connEquiv] : PropString).length
      · cases rest1 with
        | nil =>
          have h1 : PropString.leftParenCount ([] : PropString) = 0 := by decide
          have h2 : PropString.rightParenCount ([] : PropString) = 0 := by decide
          omega
        | cons c1 t1 =>
          have : t1 = [] := by
            have : (c1 :: t1).length ≤ 1 := hlen2; simp at this
            cases t1 with | nil => rfl | cons _ _ => simp at this
          subst this
          have : c1 = PropAlphabet.connEquiv := by
            obtain ⟨w, hw⟩ := prefix_of_append_eq hrest1s hlen2; simp at hw; exact hw.1
          subst this
          have h1 : PropString.leftParenCount [PropAlphabet.connEquiv] = 0 := by decide
          have h2 : PropString.rightParenCount [PropAlphabet.connEquiv] = 0 := by decide
          omega
      · obtain ⟨rest2, hrest2, hrest2s⟩ := split_past_prefix hrest1s (by omega)
        rw [hrest2, leftParenCount_append, rightParenCount_append]
        have h1 : PropString.leftParenCount [PropAlphabet.connEquiv] = 0 := by decide
        have h2 : PropString.rightParenCount [PropAlphabet.connEquiv] = 0 := by decide
        by_cases hlen3 : rest2.length ≤ B.toStr.length
        · have := toStr_prefix_lpc_ge_rpc B rest2 (prefix_of_append_eq hrest2s hlen3); omega
        · obtain ⟨rest3, hrest3, hrest3s⟩ := split_past_prefix hrest2s (by omega)
          cases rest3 with
          | nil =>
            rw [hrest3, leftParenCount_append, rightParenCount_append]
            have hbalB := propFormula_balanced_parens B
            have h3 : PropString.leftParenCount ([] : PropString) = 0 := by decide
            have h4 : PropString.rightParenCount ([] : PropString) = 0 := by decide
            omega
          | cons c3 t3 =>
            have ht3s : t3 ++ suffix = [] := by
              have := List.tail_eq_of_cons_eq hrest3s; simpa using this
            have : t3 = [] := by cases t3 with | nil => rfl | cons _ _ => simp at ht3s
            subst this
            have : suffix = [] := by simpa using ht3s
            exact absurd this hsuffix_ne

helper /-- Any proper prefix of a proposition's string representation is either
    empty, a string of negation symbols, or has an excess of left parentheses. -/
theorem propFormula_proper_prefix_structure (A : PropFormula)
    (p : PropString) (hpre : p <+: A.toStr) (hne : p ≠ A.toStr) :
    p = [] ∨ (∀ c, c ∈ p → c = PropAlphabet.connNot) ∨
    p.leftParenCount > p.rightParenCount :=
-- BEGIN PROOF
by
  induction A generalizing p with
  | var n =>
    obtain ⟨suffix, hsuffix⟩ := hpre
    simp only [PropFormula.toStr] at hsuffix hne
    cases p with
    | nil => left; rfl
    | cons ph pt =>
      have hph : ph = PropAlphabet.propSym n := List.head_eq_of_cons_eq hsuffix
      have htl : pt ++ suffix = [] := by
        have := List.tail_eq_of_cons_eq hsuffix; simpa using this
      have hpt : pt = [] := by
        cases pt with
        | nil => rfl
        | cons _ _ => simp at htl
      subst hph; subst hpt; simp at htl; subst htl
      exfalso; exact hne rfl
  | fls =>
    obtain ⟨suffix, hsuffix⟩ := hpre
    simp only [PropFormula.toStr] at hsuffix hne
    cases p with
    | nil => left; rfl
    | cons ph pt =>
      have hph : ph = PropAlphabet.falsum := List.head_eq_of_cons_eq hsuffix
      have htl : pt ++ suffix = [] := by
        have := List.tail_eq_of_cons_eq hsuffix; simpa using this
      have hpt : pt = [] := by
        cases pt with
        | nil => rfl
        | cons _ _ => simp at htl
      subst hph; subst hpt; simp at htl; subst htl
      exfalso; exact hne rfl
  | neg A ih =>
    obtain ⟨suffix, hsuffix⟩ := hpre
    simp only [PropFormula.toStr, FormationFn.c_neg] at hsuffix hne
    cases p with
    | nil => left; rfl
    | cons ph pt =>
      have hph : ph = PropAlphabet.connNot := by
        have := List.head_eq_of_cons_eq hsuffix; exact this
      have htl : pt ++ suffix = A.toStr := by
        have := List.tail_eq_of_cons_eq hsuffix; simpa using this
      subst hph
      have hpt_prefix : pt <+: A.toStr := ⟨suffix, htl⟩
      by_cases hpt_eq : pt = A.toStr
      · subst hpt_eq; simp at htl; subst htl; exfalso; exact hne rfl
      · have ih_result := ih pt hpt_prefix hpt_eq
        rcases ih_result with rfl | hall | hgt
        · right; left; intro c hc; simp at hc; exact hc
        · right; left; intro c hc
          simp at hc
          rcases hc with rfl | hc
          · rfl
          · exact hall c hc
        · right; right
          rw [show (PropAlphabet.connNot :: pt : PropString) = [PropAlphabet.connNot] ++ pt from rfl]
          rw [leftParenCount_append, rightParenCount_append]
          have h1 : PropString.leftParenCount [PropAlphabet.connNot] = 0 := by decide
          have h2 : PropString.rightParenCount [PropAlphabet.connNot] = 0 := by decide
          omega
  | conj A B _ _ => exact proper_prefix_conj A B p hpre hne
  | disj A B _ _ => exact proper_prefix_disj A B p hpre hne
  | impl A B _ _ => exact proper_prefix_impl A B p hpre hne
  | equiv_ A B _ _ => exact proper_prefix_equiv_ A B p hpre hne

helper /-- No proper prefix of a proposition's string representation is itself a
    proposition's string representation. -/
theorem propFormula_proper_prefix_not_prop (B : PropFormula) (p : PropString)
    (hpre : p <+: B.toStr) (hne : p ≠ B.toStr) :
    ¬(∃ C : PropFormula, C.toStr = p) :=
-- BEGIN PROOF
by
  intro ⟨C, hC⟩
  have hstruct := propFormula_proper_prefix_structure B p hpre hne
  have hbal := propFormula_balanced_parens C
  rw [hC] at hbal
  rcases hstruct with rfl | hall | hgt
  · -- p = [], but C.toStr is never empty
    exact toStr_ne_nil C hC
  · -- all chars in p are connNot
    subst hC
    have ⟨c, hc, hne_not⟩ := toStr_has_non_connNot C
    exact absurd (hall c hc) hne_not
  · -- p has more left than right parens, contradicting balanced
    omega

proof_of propFormula_parenthesis_balance := by
  -- BEGIN PROOF
    exact ⟨propFormula_balanced_parens, propFormula_proper_prefix_structure,
      propFormula_proper_prefix_not_prop⟩


helper /-- Equal strings beginning with propositions have the same first proposition. -/
theorem toStr_append_cancel (A B : PropFormula) (s t : PropString)
    (h : A.toStr ++ s = B.toStr ++ t) : A.toStr = B.toStr ∧ s = t := by
  have heq : A.toStr = B.toStr := by
    by_cases hlen : A.toStr.length ≤ B.toStr.length
    · by_cases heq : A.toStr = B.toStr
      · exact heq
      · exact False.elim (propFormula_proper_prefix_not_prop B A.toStr
          (prefix_of_append_eq h hlen) heq ⟨A, rfl⟩)
    · by_cases heq : A.toStr = B.toStr
      · exact heq
      · exact False.elim (propFormula_proper_prefix_not_prop A B.toStr
          (prefix_of_append_eq h.symm (by omega)) (Ne.symm heq) ⟨B, rfl⟩)
  refine ⟨heq, ?_⟩
  rw [heq] at h
  exact List.append_cancel_left h

proof_of PropFormula.toStr_injective := by
  induction A generalizing B <;> cases B <;>
    simp only [PropFormula.toStr, FormationFn.c_neg, FormationFn.c_conj,
      FormationFn.c_disj, FormationFn.c_impl, FormationFn.c_equiv,
      List.append_assoc, List.singleton_append, List.cons.injEq] at h
  all_goals simp at h ⊢
  case var.var => exact h
  case neg.neg A ih B => exact ih h
  all_goals obtain ⟨hleft, hrest⟩ := toStr_append_cancel _ _ _ _ h
  all_goals simp at hrest
  all_goals constructor <;> (apply_assumption; assumption)


proof_of propFormula_free_generation := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩ h
    have heq : PropFormula.neg a = PropFormula.neg b :=
      PropFormula.toStr_injective h
    cases heq
    rfl
  · rintro A B C D ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
    have heq : PropFormula.conj a b = PropFormula.conj c d :=
      PropFormula.toStr_injective h
    cases heq
    exact ⟨rfl, rfl⟩
  · rintro A B C D ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
    have heq : PropFormula.disj a b = PropFormula.disj c d :=
      PropFormula.toStr_injective h
    cases heq
    exact ⟨rfl, rfl⟩
  · rintro A B C D ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
    have heq : PropFormula.impl a b = PropFormula.impl c d :=
      PropFormula.toStr_injective h
    cases heq
    exact ⟨rfl, rfl⟩
  · rintro A B C D ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
    have heq : PropFormula.equiv_ a b = PropFormula.equiv_ c d :=
      PropFormula.toStr_injective h
    cases heq
    exact ⟨rfl, rfl⟩
  · rintro A B C ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ h
    have heq : PropFormula.neg a = PropFormula.conj b c :=
      PropFormula.toStr_injective h
    cases heq
  · rintro A B C ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ h
    have heq : PropFormula.neg a = PropFormula.disj b c :=
      PropFormula.toStr_injective h
    cases heq
  · rintro A B C ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ h
    have heq : PropFormula.neg a = PropFormula.impl b c :=
      PropFormula.toStr_injective h
    cases heq
  · rintro A B C ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ h
    have heq : PropFormula.neg a = PropFormula.equiv_ b c :=
      PropFormula.toStr_injective h
    cases heq
  · rintro A B C D ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
    have heq : PropFormula.conj a b = PropFormula.disj c d :=
      PropFormula.toStr_injective h
    cases heq
  · rintro A B C D ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
    have heq : PropFormula.conj a b = PropFormula.impl c d :=
      PropFormula.toStr_injective h
    cases heq
  · rintro A B C D ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
    have heq : PropFormula.conj a b = PropFormula.equiv_ c d :=
      PropFormula.toStr_injective h
    cases heq
  · rintro A B C D ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
    have heq : PropFormula.disj a b = PropFormula.impl c d :=
      PropFormula.toStr_injective h
    cases heq
  · rintro A B C D ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
    have heq : PropFormula.disj a b = PropFormula.equiv_ c d :=
      PropFormula.toStr_injective h
    cases heq
  · rintro A B C D ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩ ⟨d, rfl⟩ h
    have heq : PropFormula.impl a b = PropFormula.equiv_ c d :=
      PropFormula.toStr_injective h
    cases heq
  · rintro A ⟨a, rfl⟩
    constructor
    · intro n h
      have heq : PropFormula.neg a = .var n := PropFormula.toStr_injective h
      cases heq
    · intro h
      have heq : PropFormula.neg a = .fls := PropFormula.toStr_injective h
      cases heq
  · rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
    constructor
    · intro n h
      have heq : PropFormula.conj a b = .var n := PropFormula.toStr_injective h
      cases heq
    · intro h
      have heq : PropFormula.conj a b = .fls := PropFormula.toStr_injective h
      cases heq
  · rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
    constructor
    · intro n h
      have heq : PropFormula.disj a b = .var n := PropFormula.toStr_injective h
      cases heq
    · intro h
      have heq : PropFormula.disj a b = .fls := PropFormula.toStr_injective h
      cases heq
  · rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
    constructor
    · intro n h
      have heq : PropFormula.impl a b = .var n := PropFormula.toStr_injective h
      cases heq
    · intro h
      have heq : PropFormula.impl a b = .fls := PropFormula.toStr_injective h
      cases heq
  · rintro A B ⟨a, rfl⟩ ⟨b, rfl⟩
    constructor
    · intro n h
      have heq : PropFormula.equiv_ a b = .var n := PropFormula.toStr_injective h
      cases heq
    · intro h
      have heq : PropFormula.equiv_ a b = .fls := PropFormula.toStr_injective h
      cases heq


proof_of exEmptyParens_not_formula := by
  rintro ⟨A, h⟩
  have positive (B : PropFormula) : 0 < B.toStr.length :=
    List.length_pos_iff.mpr (toStr_ne_nil B)
  cases A <;>
    simp [PropFormula.toStr, FormationFn.c_neg, FormationFn.c_conj,
      FormationFn.c_disj, FormationFn.c_impl, FormationFn.c_equiv] at h
  all_goals have hlen := congrArg List.length h
  all_goals simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  all_goals rename_i A B
  all_goals have := positive A
  all_goals have := positive B
  all_goals omega


proof_of exTrailingConjunction_not_formula := by
  rintro ⟨A, h⟩
  apply propFormula_proper_prefix_not_prop A exP1orP2.toStr
  · exact ⟨[.connAnd], h.symm⟩
  · rw [h]
    decide
  · exact ⟨exP1orP2, rfl⟩


end LCS.Propositional.Syntax
