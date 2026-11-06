import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.TreeTransport

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

private theorem finiteSet_of_finset {α : Type}
    (s : LCS.Finset α) : Set.Finite (fun a => a ∈ s) :=
  ⟨s.toList, fun a => (LCS.Finset.mem_toList s a).symm⟩

private theorem finiteSet_of_finset_cover {α : Type}
    {S : Set α} (s : LCS.Finset α)
    (hS : ∀ a, S a → a ∈ s) : Set.Finite S :=
  Set.Finite.subset (finiteSet_of_finset s) hS

private noncomputable def finsetOfFiniteSet {α : Type}
    [DecidableEq α] (S : Set α) (hS : Set.Finite S) : LCS.Finset α :=
  LCS.Finset.ofList (Classical.choose hS)

private theorem mem_finsetOfFiniteSet {α : Type}
    [DecidableEq α] (S : Set α) (hS : Set.Finite S) (a : α) :
    a ∈ finsetOfFiniteSet S hS ↔ S a := by
  rw [finsetOfFiniteSet, LCS.Finset.mem_ofList]
  exact (Classical.choose_spec hS a).symm

private theorem mem_insert_represents_left {α : Type}
    [DecidableEq α] {S : Set α} {s : LCS.Finset α}
    (a : α) (hs : ∀ x, x ∈ s ↔ S x) (x : α) :
    x ∈ LCS.Finset.insert a s ↔ x = a ∨ S x := by
  rw [LCS.Finset.mem_insert, hs x]

private theorem mem_insert_represents_right {α : Type}
    [DecidableEq α] {S : Set α} {s : LCS.Finset α}
    (a : α) (hs : ∀ x, x ∈ s ↔ S x) (x : α) :
    x ∈ LCS.Finset.insert a s ↔ S x ∨ x = a := by
  rw [LCS.Finset.mem_insert, hs x, or_comm]

theorem finset_insert_eq_self_of_mem {α : Type}
    [DecidableEq α] {a : α} {s : LCS.Finset α}
    (ha : a ∈ s) : LCS.Finset.insert a s = s := by
  apply LCS.Finset.ext
  intro x
  rw [LCS.Finset.mem_insert]
  constructor
  · rintro (rfl | hx)
    · exact ha
    · exact hx
  · exact Or.inr

/-- A finite set-level G1nnf derivation gives an indexed proof tree for
any Finset representatives of its endpoint sets.  Finiteness is recovered
from the supplied representatives at each recursive step.  No proof-tree
weakening is used: each rule is rebuilt with an exact representative of
its ambient set, which is essential for preserving eigenvariable side
conditions. -/
theorem g1nnfProofTree_of_setDerivable
    {L : Language} {hL : L.withoutEquality}
    {S T : Set (FormulaN L)}
    (hDer : G1nnfSetDerivable S T)
    {Γ Δ : LCS.Finset (FormulaN L)}
    (hΓ : ∀ F, F ∈ Γ ↔ S F)
    (hΔ : ∀ F, F ∈ Δ ↔ T F)
    (hNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ)) :
    Nonempty (G1nnfProofTree hL Γ Δ) := by
  induction hDer generalizing Γ Δ with
  | axiomPos A hAtom S T hS hT =>
      have hAΓ : A ∈ Γ := (hΓ A).2 hS
      have hAΔ : A ∈ Δ := (hΔ A).2 hT
      have hANNF : A.isNNF := hNNF.1 A hAΓ
      have hΓeq : LCS.Finset.insert A Γ = Γ :=
        finset_insert_eq_self_of_mem hAΓ
      have hΔeq : LCS.Finset.insert A Δ = Δ :=
        finset_insert_eq_self_of_mem hAΔ
      let tree :=
        G1nnfProofTree.axiom_ (hL := hL)
          (.axiomPosAtomic A hAtom Γ Δ) Γ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hANNF
              (G1nnfFinsetSequent.IsNNF.insert_left hANNF hNNF)⟩
      exact ⟨tree.castTree hΓeq hΔeq⟩
  | axiomNeg A hAtom S T hS hT =>
      have hAΓ : FormulaN.neg A ∈ Γ := (hΓ (FormulaN.neg A)).2 hS
      have hAΔ : FormulaN.neg A ∈ Δ := (hΔ (FormulaN.neg A)).2 hT
      have hANNF : (FormulaN.neg A).isNNF := hNNF.1 _ hAΓ
      have hΓeq : LCS.Finset.insert (FormulaN.neg A) Γ = Γ :=
        finset_insert_eq_self_of_mem hAΓ
      have hΔeq : LCS.Finset.insert (FormulaN.neg A) Δ = Δ :=
        finset_insert_eq_self_of_mem hAΔ
      let tree :=
        G1nnfProofTree.axiom_ (hL := hL)
          (.axiomNegAtomic A hAtom Γ Δ) Γ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hANNF
              (G1nnfFinsetSequent.IsNNF.insert_left hANNF hNNF)⟩
      exact ⟨tree.castTree hΓeq hΔeq⟩
  | axiomCompL A hAtom S T hA hNA =>
      have hAΓ : A ∈ Γ := (hΓ A).2 hA
      have hNAΓ : FormulaN.neg A ∈ Γ := (hΓ (FormulaN.neg A)).2 hNA
      have hANNF : A.isNNF := hNNF.1 A hAΓ
      have hNANNF : (FormulaN.neg A).isNNF := hNNF.1 _ hNAΓ
      have hNAeq : LCS.Finset.insert (FormulaN.neg A) Γ = Γ :=
        finset_insert_eq_self_of_mem hNAΓ
      have hΓeq :
          LCS.Finset.insert A (LCS.Finset.insert (FormulaN.neg A) Γ) = Γ := by
        rw [hNAeq]
        exact finset_insert_eq_self_of_mem hAΓ
      let tree :=
        G1nnfProofTree.axiom_ (hL := hL)
          (.axiomCompLeft A hAtom Γ Δ) Γ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_left hANNF
              (G1nnfFinsetSequent.IsNNF.insert_left hNANNF hNNF)⟩
      exact ⟨tree.castTree hΓeq rfl⟩
  | axiomCompR A hAtom S T hA hNA =>
      have hAΔ : A ∈ Δ := (hΔ A).2 hA
      have hNAΔ : FormulaN.neg A ∈ Δ := (hΔ (FormulaN.neg A)).2 hNA
      have hANNF : A.isNNF := hNNF.2 A hAΔ
      have hNANNF : (FormulaN.neg A).isNNF := hNNF.2 _ hNAΔ
      have hNAeq : LCS.Finset.insert (FormulaN.neg A) Δ = Δ :=
        finset_insert_eq_self_of_mem hNAΔ
      have hΔeq :
          LCS.Finset.insert A (LCS.Finset.insert (FormulaN.neg A) Δ) = Δ := by
        rw [hNAeq]
        exact finset_insert_eq_self_of_mem hAΔ
      let tree :=
        G1nnfProofTree.axiom_ (hL := hL)
          (.axiomCompRight A hAtom Γ Δ) Γ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hANNF
              (G1nnfFinsetSequent.IsNNF.insert_right hNANNF hNNF)⟩
      exact ⟨tree.castTree rfl hΔeq⟩
  | cut A S T hANNF h1 h2 ih1 ih2 =>
      obtain ⟨sub1⟩ :=
        ih1 hΓ (mem_insert_represents_right A hΔ)
          (G1nnfFinsetSequent.IsNNF.insert_right hANNF hNNF)
      obtain ⟨sub2⟩ :=
        ih2 (mem_insert_represents_left A hΓ) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hANNF hNNF)
      have hConc := G1nnfRule.cut_shared_conclusion A Γ Δ
      have hAC : G1nnfRule.ApplicationConditions (.cut A Γ Δ) Γ Δ := by
        refine ⟨trivial, ?_⟩
        simpa only [hConc] using hNNF
      let tree :=
        G1nnfProofTree.twoPremise (.cut A Γ Δ) Γ Δ rfl hAC sub1 sub2
      exact ⟨tree.castTree (congrArg Prod.fst hConc) (congrArg Prod.snd hConc)⟩
  | conjR A B S T h1 h2 ih1 ih2 =>
      have hTFinite : Set.Finite T :=
        finiteSet_of_finset_cover Δ
          (fun F hFT => (hΔ F).2 (Or.inl hFT))
      let Δ₀ := finsetOfFiniteSet T hTFinite
      have hΔ₀ : ∀ F, F ∈ Δ₀ ↔ T F :=
        mem_finsetOfFiniteSet T hTFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ₀) := by
        refine ⟨hNNF.1, ?_⟩
        intro F hF
        exact hNNF.2 F ((hΔ F).2 (Or.inl ((hΔ₀ F).1 hF)))
      have hConjNNF : (FormulaN.conj A B).isNNF :=
        hNNF.2 _ ((hΔ _).2 (Or.inr rfl))
      obtain ⟨sub1⟩ :=
        ih1 hΓ (mem_insert_represents_right A hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hConjNNF.1 hBaseNNF)
      obtain ⟨sub2⟩ :=
        ih2 hΓ (mem_insert_represents_right B hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hConjNNF.2 hBaseNNF)
      let tree :=
        G1nnfProofTree.twoPremise (.conjRight A B) Γ Δ₀ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hConjNNF hBaseNNF⟩
          sub1 sub2
      have hΔeq : LCS.Finset.insert (FormulaN.conj A B) Δ₀ = Δ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_right (FormulaN.conj A B) hΔ₀ F).trans
            (hΔ F).symm)
      exact ⟨tree.castTree rfl hΔeq⟩
  | conjL1 A B S T h ih =>
      have hSFinite : Set.Finite S :=
        finiteSet_of_finset_cover Γ
          (fun F hFS => (hΓ F).2 (Or.inr hFS))
      let Γ₀ := finsetOfFiniteSet S hSFinite
      have hΓ₀ : ∀ F, F ∈ Γ₀ ↔ S F :=
        mem_finsetOfFiniteSet S hSFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ₀, Δ) := by
        refine ⟨?_, hNNF.2⟩
        intro F hF
        exact hNNF.1 F ((hΓ F).2 (Or.inr ((hΓ₀ F).1 hF)))
      have hConjNNF : (FormulaN.conj A B).isNNF :=
        hNNF.1 _ ((hΓ _).2 (Or.inl rfl))
      obtain ⟨sub⟩ :=
        ih (mem_insert_represents_left A hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hConjNNF.1 hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.conjLeft1 A B) Γ₀ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_left hConjNNF hBaseNNF⟩ sub
      have hΓeq : LCS.Finset.insert (FormulaN.conj A B) Γ₀ = Γ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_left (FormulaN.conj A B) hΓ₀ F).trans
            (hΓ F).symm)
      exact ⟨tree.castTree hΓeq rfl⟩
  | conjL2 A B S T h ih =>
      have hSFinite : Set.Finite S :=
        finiteSet_of_finset_cover Γ
          (fun F hFS => (hΓ F).2 (Or.inr hFS))
      let Γ₀ := finsetOfFiniteSet S hSFinite
      have hΓ₀ : ∀ F, F ∈ Γ₀ ↔ S F :=
        mem_finsetOfFiniteSet S hSFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ₀, Δ) := by
        refine ⟨?_, hNNF.2⟩
        intro F hF
        exact hNNF.1 F ((hΓ F).2 (Or.inr ((hΓ₀ F).1 hF)))
      have hConjNNF : (FormulaN.conj A B).isNNF :=
        hNNF.1 _ ((hΓ _).2 (Or.inl rfl))
      obtain ⟨sub⟩ :=
        ih (mem_insert_represents_left B hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hConjNNF.2 hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.conjLeft2 A B) Γ₀ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_left hConjNNF hBaseNNF⟩ sub
      have hΓeq : LCS.Finset.insert (FormulaN.conj A B) Γ₀ = Γ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_left (FormulaN.conj A B) hΓ₀ F).trans
            (hΓ F).symm)
      exact ⟨tree.castTree hΓeq rfl⟩
  | disjL A B S T h1 h2 ih1 ih2 =>
      have hSFinite : Set.Finite S :=
        finiteSet_of_finset_cover Γ
          (fun F hFS => (hΓ F).2 (Or.inr hFS))
      let Γ₀ := finsetOfFiniteSet S hSFinite
      have hΓ₀ : ∀ F, F ∈ Γ₀ ↔ S F :=
        mem_finsetOfFiniteSet S hSFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ₀, Δ) := by
        refine ⟨?_, hNNF.2⟩
        intro F hF
        exact hNNF.1 F ((hΓ F).2 (Or.inr ((hΓ₀ F).1 hF)))
      have hDisjNNF : (FormulaN.disj A B).isNNF :=
        hNNF.1 _ ((hΓ _).2 (Or.inl rfl))
      obtain ⟨sub1⟩ :=
        ih1 (mem_insert_represents_left A hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hDisjNNF.1 hBaseNNF)
      obtain ⟨sub2⟩ :=
        ih2 (mem_insert_represents_left B hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hDisjNNF.2 hBaseNNF)
      let tree :=
        G1nnfProofTree.twoPremise (.disjLeft A B) Γ₀ Δ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_left hDisjNNF hBaseNNF⟩
          sub1 sub2
      have hΓeq : LCS.Finset.insert (FormulaN.disj A B) Γ₀ = Γ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_left (FormulaN.disj A B) hΓ₀ F).trans
            (hΓ F).symm)
      exact ⟨tree.castTree hΓeq rfl⟩
  | disjR1 A B S T h ih =>
      have hTFinite : Set.Finite T :=
        finiteSet_of_finset_cover Δ
          (fun F hFT => (hΔ F).2 (Or.inl hFT))
      let Δ₀ := finsetOfFiniteSet T hTFinite
      have hΔ₀ : ∀ F, F ∈ Δ₀ ↔ T F :=
        mem_finsetOfFiniteSet T hTFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ₀) := by
        refine ⟨hNNF.1, ?_⟩
        intro F hF
        exact hNNF.2 F ((hΔ F).2 (Or.inl ((hΔ₀ F).1 hF)))
      have hDisjNNF : (FormulaN.disj A B).isNNF :=
        hNNF.2 _ ((hΔ _).2 (Or.inr rfl))
      obtain ⟨sub⟩ :=
        ih hΓ (mem_insert_represents_right A hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hDisjNNF.1 hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.disjRight1 A B) Γ Δ₀ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hDisjNNF hBaseNNF⟩ sub
      have hΔeq : LCS.Finset.insert (FormulaN.disj A B) Δ₀ = Δ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_right (FormulaN.disj A B) hΔ₀ F).trans
            (hΔ F).symm)
      exact ⟨tree.castTree rfl hΔeq⟩
  | disjR2 A B S T h ih =>
      have hTFinite : Set.Finite T :=
        finiteSet_of_finset_cover Δ
          (fun F hFT => (hΔ F).2 (Or.inl hFT))
      let Δ₀ := finsetOfFiniteSet T hTFinite
      have hΔ₀ : ∀ F, F ∈ Δ₀ ↔ T F :=
        mem_finsetOfFiniteSet T hTFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ₀) := by
        refine ⟨hNNF.1, ?_⟩
        intro F hF
        exact hNNF.2 F ((hΔ F).2 (Or.inl ((hΔ₀ F).1 hF)))
      have hDisjNNF : (FormulaN.disj A B).isNNF :=
        hNNF.2 _ ((hΔ _).2 (Or.inr rfl))
      obtain ⟨sub⟩ :=
        ih hΓ (mem_insert_represents_right B hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hDisjNNF.2 hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.disjRight2 A B) Γ Δ₀ rfl
          ⟨trivial,
            G1nnfFinsetSequent.IsNNF.insert_right hDisjNNF hBaseNNF⟩ sub
      have hΔeq : LCS.Finset.insert (FormulaN.disj A B) Δ₀ = Δ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_right (FormulaN.disj A B) hΔ₀ F).trans
            (hΔ F).symm)
      exact ⟨tree.castTree rfl hΔeq⟩
  | allL x A t S T hFreeFor h ih =>
      have hSFinite : Set.Finite S :=
        finiteSet_of_finset_cover Γ
          (fun F hFS => (hΓ F).2 (Or.inr hFS))
      let Γ₀ := finsetOfFiniteSet S hSFinite
      have hΓ₀ : ∀ F, F ∈ Γ₀ ↔ S F :=
        mem_finsetOfFiniteSet S hSFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ₀, Δ) := by
        refine ⟨?_, hNNF.2⟩
        intro F hF
        exact hNNF.1 F ((hΓ F).2 (Or.inr ((hΓ₀ F).1 hF)))
      have hAllNNF : (FormulaN.all x A).isNNF :=
        hNNF.1 _ ((hΓ _).2 (Or.inl rfl))
      have hSubstNNF : (formulaSubstN A t x).isNNF :=
        isNNF_formulaSubstN A t x hAllNNF
      obtain ⟨sub⟩ :=
        ih (mem_insert_represents_left (formulaSubstN A t x) hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hSubstNNF hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.allLeft x A t) Γ₀ Δ rfl
          ⟨hFreeFor,
            G1nnfFinsetSequent.IsNNF.insert_left hAllNNF hBaseNNF⟩ sub
      have hΓeq : LCS.Finset.insert (FormulaN.all x A) Γ₀ = Γ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_left (FormulaN.all x A) hΓ₀ F).trans
            (hΓ F).symm)
      exact ⟨tree.castTree hΓeq rfl⟩
  | allR x A y S T hFreeFor hFreshS hFreshT hFreshAll h ih =>
      have hTFinite : Set.Finite T :=
        finiteSet_of_finset_cover Δ
          (fun F hFT => (hΔ F).2 (Or.inl hFT))
      let Δ₀ := finsetOfFiniteSet T hTFinite
      have hΔ₀ : ∀ F, F ∈ Δ₀ ↔ T F :=
        mem_finsetOfFiniteSet T hTFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ₀) := by
        refine ⟨hNNF.1, ?_⟩
        intro F hF
        exact hNNF.2 F ((hΔ F).2 (Or.inl ((hΔ₀ F).1 hF)))
      have hAllNNF : (FormulaN.all x A).isNNF :=
        hNNF.2 _ ((hΔ _).2 (Or.inr rfl))
      have hSubstNNF : (formulaSubstN A (.var y) x).isNNF :=
        isNNF_formulaSubstN A (.var y) x hAllNNF
      obtain ⟨sub⟩ :=
        ih hΓ
          (mem_insert_represents_right (formulaSubstN A (.var y) x) hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hSubstNNF hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.allRight x A y) Γ Δ₀ rfl
          ⟨⟨hFreeFor, hFreshAll,
              fun F hF => hFreshS F ((hΓ F).1 hF),
              fun F hF => hFreshT F ((hΔ₀ F).1 hF)⟩,
            G1nnfFinsetSequent.IsNNF.insert_right hAllNNF hBaseNNF⟩ sub
      have hΔeq : LCS.Finset.insert (FormulaN.all x A) Δ₀ = Δ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_right (FormulaN.all x A) hΔ₀ F).trans
            (hΔ F).symm)
      exact ⟨tree.castTree rfl hΔeq⟩
  | exL x A y S T hFreeFor hFreshS hFreshT hFreshEx h ih =>
      have hSFinite : Set.Finite S :=
        finiteSet_of_finset_cover Γ
          (fun F hFS => (hΓ F).2 (Or.inr hFS))
      let Γ₀ := finsetOfFiniteSet S hSFinite
      have hΓ₀ : ∀ F, F ∈ Γ₀ ↔ S F :=
        mem_finsetOfFiniteSet S hSFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ₀, Δ) := by
        refine ⟨?_, hNNF.2⟩
        intro F hF
        exact hNNF.1 F ((hΓ F).2 (Or.inr ((hΓ₀ F).1 hF)))
      have hExNNF : (FormulaN.ex x A).isNNF :=
        hNNF.1 _ ((hΓ _).2 (Or.inl rfl))
      have hSubstNNF : (formulaSubstN A (.var y) x).isNNF :=
        isNNF_formulaSubstN A (.var y) x hExNNF
      obtain ⟨sub⟩ :=
        ih
          (mem_insert_represents_left (formulaSubstN A (.var y) x) hΓ₀) hΔ
          (G1nnfFinsetSequent.IsNNF.insert_left hSubstNNF hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.exLeft x A y) Γ₀ Δ rfl
          ⟨⟨hFreeFor, hFreshEx,
              fun F hF => hFreshS F ((hΓ₀ F).1 hF),
              fun F hF => hFreshT F ((hΔ F).1 hF)⟩,
            G1nnfFinsetSequent.IsNNF.insert_left hExNNF hBaseNNF⟩ sub
      have hΓeq : LCS.Finset.insert (FormulaN.ex x A) Γ₀ = Γ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_left (FormulaN.ex x A) hΓ₀ F).trans
            (hΓ F).symm)
      exact ⟨tree.castTree hΓeq rfl⟩
  | exR x A t S T hFreeFor h ih =>
      have hTFinite : Set.Finite T :=
        finiteSet_of_finset_cover Δ
          (fun F hFT => (hΔ F).2 (Or.inl hFT))
      let Δ₀ := finsetOfFiniteSet T hTFinite
      have hΔ₀ : ∀ F, F ∈ Δ₀ ↔ T F :=
        mem_finsetOfFiniteSet T hTFinite
      have hBaseNNF : G1nnfFinsetSequent.IsNNF (Γ, Δ₀) := by
        refine ⟨hNNF.1, ?_⟩
        intro F hF
        exact hNNF.2 F ((hΔ F).2 (Or.inl ((hΔ₀ F).1 hF)))
      have hExNNF : (FormulaN.ex x A).isNNF :=
        hNNF.2 _ ((hΔ _).2 (Or.inr rfl))
      have hSubstNNF : (formulaSubstN A t x).isNNF :=
        isNNF_formulaSubstN A t x hExNNF
      obtain ⟨sub⟩ :=
        ih hΓ
          (mem_insert_represents_right (formulaSubstN A t x) hΔ₀)
          (G1nnfFinsetSequent.IsNNF.insert_right hSubstNNF hBaseNNF)
      let tree :=
        G1nnfProofTree.onePremise (.exRight x A t) Γ Δ₀ rfl
          ⟨hFreeFor,
            G1nnfFinsetSequent.IsNNF.insert_right hExNNF hBaseNNF⟩ sub
      have hΔeq : LCS.Finset.insert (FormulaN.ex x A) Δ₀ = Δ :=
        LCS.Finset.ext (fun F =>
          (mem_insert_represents_right (FormulaN.ex x A) hΔ₀ F).trans
            (hΔ F).symm)
      exact ⟨tree.castTree rfl hΔeq⟩

end LCS.CutElim.Hauptsatz
end
