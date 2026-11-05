import LCS.FirstOrder.ManySorted

namespace LCS.FirstOrder.ManySorted

proof_of sort_nonempty := ⟨L.someSort⟩
  -- BEGIN PROOF








helper /-- Internal AST term facts used in the syntactic presentation: constructor-kind
separation, fixed-label injectivity and strictly increasing structural size.
The string-level freeness statement is in ManySorted.SyntaxAlgebra. -/
theorem msTerm_free_generation (L : MSLanguage) :
    -- Part 1: Distinct constructor ranges within each sort
    (∀ (s : L.SortType) (n : Nat) (c : L.constSymbols s),
        MSTerm.var (L := L) s n ≠ MSTerm.const s c) ∧
    (∀ (f : L.funSymbols) (n : Nat)
        (ts : (i : Fin (L.funRank f).1.length) →
          MSTerm L ((L.funRank f).1.get i)),
        MSTerm.var (L := L) (L.funRank f).2 n ≠ MSTerm.func f ts) ∧
    (∀ (f : L.funSymbols) (c : L.constSymbols (L.funRank f).2)
        (ts : (i : Fin (L.funRank f).1.length) →
          MSTerm L ((L.funRank f).1.get i)),
        MSTerm.const (L := L) (L.funRank f).2 c ≠ MSTerm.func f ts) ∧
    -- Part 2: Each constructor is injective on its arguments
    (∀ (s : L.SortType) (n1 n2 : Nat),
        MSTerm.var (L := L) s n1 = MSTerm.var (L := L) s n2 → n1 = n2) ∧
    (∀ (s : L.SortType) (c1 c2 : L.constSymbols s),
        MSTerm.const (L := L) s c1 = MSTerm.const (L := L) s c2 →
          c1 = c2) ∧
    (∀ (f : L.funSymbols)
        (ts us : (i : Fin (L.funRank f).1.length) →
          MSTerm L ((L.funRank f).1.get i)),
        MSTerm.func f ts = MSTerm.func f us → ts = us) ∧
    -- Part 3: Function-symbol constructors strictly increase msTermSize
    (∀ (f : L.funSymbols)
        (ts : (i : Fin (L.funRank f).1.length) →
          MSTerm L ((L.funRank f).1.get i))
        (i : Fin (L.funRank f).1.length),
        msTermSize (ts i) < msTermSize (MSTerm.func f ts)) :=
-- BEGIN PROOF
by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ h; cases h
  · intro _ _ _ h; cases h
  · intro _ _ _ h; cases h
  · intro _ _ _ h; injection h
  · intro _ _ _ h; injection h
  · intro _ _ _ h; injection h
  · intro f ts i
    simp only [msTermSize]
    have := msTermSize_foldl_ofFn_ge_elem (L.funRank f).1.get ts i
    omega



namespace MSFormula



end MSFormula







end LCS.FirstOrder.ManySorted
