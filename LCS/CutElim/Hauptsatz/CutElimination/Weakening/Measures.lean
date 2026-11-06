import LCS.Item
import LCS.Util
import LCS.CutElim.Hauptsatz
import LCS.CutElim.Hauptsatz.Completeness
import LCS.CutElim.Hauptsatz.CutElimination.ProofTrees
import LCS.CutElim.Hauptsatz.CutElimination.CutRank
import LCS.CutElim.Hauptsatz.CutElimination.Eigenvariables
import LCS.CutElim.Hauptsatz.CutElimination.Weakening.Constructions

section
open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SyntaxN.Variables
open LCS.FirstOrder.SyntaxN.Substitution
open LCS.CutElim.Hauptsatz
open LCS.CutElim.Hauptsatz.Completeness
namespace LCS.CutElim.Hauptsatz

theorem G1nnfProofTree.depth_mpr_left {L : Language} {hL : L.withoutEquality}
    {Γ Γ' Δ : LCS.Finset (FormulaN L)}
    (hidx : Γ = Γ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ' Δ)
    (T : G1nnfProofTree hL Γ' Δ) :
    (@G1nnfProofTree.depth L hL Γ Δ
      (@Eq.mpr (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ' Δ) htype T)) =
      (@G1nnfProofTree.depth L hL Γ' Δ T) := by
  subst Γ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.depth_mp {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ' Δ')
    (T : G1nnfProofTree hL Γ Δ) :
    (@G1nnfProofTree.depth L hL Γ' Δ'
      (@Eq.mp (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ' Δ') htype T)) =
      (@G1nnfProofTree.depth L hL Γ Δ T) := by
  subst Γ'
  subst Δ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem nat_max_congr {a b c d : Nat} (h₁ : a = b) (h₂ : c = d) :
    max a c = max b d := by
  cases h₁
  cases h₂
  rfl /- ATTACH-BLOCKER: dependency: retained front declaration references this helper -/

theorem G1nnfProofTree.weakenTreeLeft_depth {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v) :
    (T.weakenTreeLeft A hNNF hFV).depth = T.depth := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    simp only [G1nnfProofTree.weakenTreeLeft]
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_left
        rule Γ Δ A hAxiom hAC hNNF
    have hSpec := Classical.choose_spec hWeakened
    have hGamma :
        ((Classical.choose hWeakened).conclusion Γ Δ).1 =
          LCS.Finset.insert A (rule.conclusion Γ Δ).1 := by
      simpa using congrArg Prod.fst hSpec.2.2
    have hDelta :
        ((Classical.choose hWeakened).conclusion Γ Δ).2 =
          (rule.conclusion Γ Δ).2 := by
      simpa using congrArg Prod.snd hSpec.2.2
    rw [G1nnfProofTree.depth_mp hGamma hDelta]
    rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    cases rule with
    | conjLeft1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm A (.conj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm B A Γ) _ _).trans (ih _)
    | conjLeft2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm A (.conj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm C A Γ) _ _).trans (ih _)
    | disjRight1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | disjRight2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | allLeft x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm A (.all x B) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm (formulaSubstN B t x) A Γ) _ _).trans
        (ih _)
    | allRight x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | exLeft x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm A (.ex x B) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm
          (formulaSubstN B (.var y) x) A Γ) _ _).trans (ih _)
    | exRight x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    cases rule with
    | cut B Lam Theta =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_union A Γ Lam) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact nat_max_congr (ih1 _) rfl
    | conjRight B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (nat_max_congr (ih1 _) (ih2 _))
    | disjLeft B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_left
        (LCS.Finset.insert_comm A (.disj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact nat_max_congr
        ((G1nnfProofTree.depth_mpr_left
          (LCS.Finset.insert_comm B A Γ) _ _).trans (ih1 _))
        ((G1nnfProofTree.depth_mpr_left
          (LCS.Finset.insert_comm C A Γ) _ _).trans (ih2 _))
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.cutRank_mpr_left {L : Language} {hL : L.withoutEquality}
    {Γ Γ' Δ : LCS.Finset (FormulaN L)}
    (hidx : Γ = Γ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ' Δ)
    (T : G1nnfProofTree hL Γ' Δ) :
    (@G1nnfProofTree.cutRank L hL Γ Δ
      (@Eq.mpr (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ' Δ) htype T)) =
      (@G1nnfProofTree.cutRank L hL Γ' Δ T) := by
  subst Γ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.cutRank_mp {L : Language} {hL : L.withoutEquality}
    {Γ Δ Γ' Δ' : LCS.Finset (FormulaN L)}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ' Δ')
    (T : G1nnfProofTree hL Γ Δ) :
    (@G1nnfProofTree.cutRank L hL Γ' Δ'
      (@Eq.mp (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ' Δ') htype T)) =
      (@G1nnfProofTree.cutRank L hL Γ Δ T) := by
  subst Γ'
  subst Δ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.weakenTreeLeft_cutRank {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v) :
    (T.weakenTreeLeft A hNNF hFV).cutRank = T.cutRank := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    simp only [G1nnfProofTree.weakenTreeLeft]
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_left
        rule Γ Δ A hAxiom hAC hNNF
    have hSpec := Classical.choose_spec hWeakened
    have hGamma :
        ((Classical.choose hWeakened).conclusion Γ Δ).1 =
          LCS.Finset.insert A (rule.conclusion Γ Δ).1 := by
      simpa using congrArg Prod.fst hSpec.2.2
    have hDelta :
        ((Classical.choose hWeakened).conclusion Γ Δ).2 =
          (rule.conclusion Γ Δ).2 := by
      simpa using congrArg Prod.snd hSpec.2.2
    rw [G1nnfProofTree.cutRank_mp hGamma hDelta]
    rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    cases rule with
    | conjLeft1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm A (.conj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm B A Γ) _ _).trans (ih _)
    | conjLeft2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm A (.conj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm C A Γ) _ _).trans (ih _)
    | disjRight1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | disjRight2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | allLeft x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm A (.all x B) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm (formulaSubstN B t x) A Γ) _ _).trans
        (ih _)
    | allRight x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | exLeft x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm A (.ex x B) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm
          (formulaSubstN B (.var y) x) A Γ) _ _).trans (ih _)
    | exRight x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    cases rule with
    | cut B Lam Theta =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_union A Γ Lam) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank, G1nnfRule.cutFormula]
      apply congrArg (fun n => max (B.degree + 1) n)
      exact nat_max_congr (ih1 _) rfl
    | conjRight B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank, G1nnfRule.cutFormula]
      exact nat_max_congr (ih1 _) (ih2 _)
    | disjLeft B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeLeft,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_left
        (LCS.Finset.insert_comm A (.disj B C) Γ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank, G1nnfRule.cutFormula]
      exact nat_max_congr
        ((G1nnfProofTree.cutRank_mpr_left
          (LCS.Finset.insert_comm B A Γ) _ _).trans (ih1 _))
        ((G1nnfProofTree.cutRank_mpr_left
          (LCS.Finset.insert_comm C A Γ) _ _).trans (ih2 _))
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.depth_mpr_right {L : Language} {hL : L.withoutEquality}
    {Γ Δ Δ' : LCS.Finset (FormulaN L)}
    (hidx : Δ = Δ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ Δ')
    (T : G1nnfProofTree hL Γ Δ') :
    (@G1nnfProofTree.depth L hL Γ Δ
      (@Eq.mpr (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ Δ') htype T)) =
      (@G1nnfProofTree.depth L hL Γ Δ' T) := by
  subst Δ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

theorem G1nnfProofTree.weakenTreeRight_depth {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v) :
    (T.weakenTreeRight A hNNF hFV).depth = T.depth := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    simp only [G1nnfProofTree.weakenTreeRight]
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_right
        rule Γ Δ A hAxiom hAC hNNF
    have hSpec := Classical.choose_spec hWeakened
    have hGamma :
        ((Classical.choose hWeakened).conclusion Γ Δ).1 =
          (rule.conclusion Γ Δ).1 := by
      simpa using congrArg Prod.fst hSpec.2.2
    have hDelta :
        ((Classical.choose hWeakened).conclusion Γ Δ).2 =
          LCS.Finset.insert A (rule.conclusion Γ Δ).2 := by
      simpa using congrArg Prod.snd hSpec.2.2
    rw [G1nnfProofTree.depth_mp hGamma hDelta]
    rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    cases rule with
    | conjLeft1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | conjLeft2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | disjRight1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm A (.disj B C) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm B A Δ) _ _).trans (ih _)
    | disjRight2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm A (.disj B C) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm C A Δ) _ _).trans (ih _)
    | allLeft x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | allRight x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm A (.all x B) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm
          (formulaSubstN B (.var y) x) A Δ) _ _).trans (ih _)
    | exLeft x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (ih _)
    | exRight x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm A (.ex x B) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm (formulaSubstN B t x) A Δ) _ _).trans
        (ih _)
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    cases rule with
    | cut B Lam Theta =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_union A Δ Theta) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact nat_max_congr
        ((G1nnfProofTree.depth_mpr_right
          (LCS.Finset.insert_comm B A Δ) _ _).trans (ih1 _)) rfl
    | conjRight B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.depth_mpr_right
        (LCS.Finset.insert_comm A (.conj B C) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.depth]
      apply congrArg (fun n => n + 1)
      exact nat_max_congr
        ((G1nnfProofTree.depth_mpr_right
          (LCS.Finset.insert_comm B A Δ) _ _).trans (ih1 _))
        ((G1nnfProofTree.depth_mpr_right
          (LCS.Finset.insert_comm C A Δ) _ _).trans (ih2 _))
    | disjLeft B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.depth]
      exact congrArg (fun n => n + 1) (nat_max_congr (ih1 _) (ih2 _))
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem /- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace -/

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem G1nnfProofTree.cutRank_mpr_right {L : Language} {hL : L.withoutEquality}
    {Γ Δ Δ' : LCS.Finset (FormulaN L)}
    (hidx : Δ = Δ')
    (htype : G1nnfProofTree hL Γ Δ = G1nnfProofTree hL Γ Δ')
    (T : G1nnfProofTree hL Γ Δ') :
    (@G1nnfProofTree.cutRank L hL Γ Δ
      (@Eq.mpr (G1nnfProofTree hL Γ Δ) (G1nnfProofTree hL Γ Δ') htype T)) =
      (@G1nnfProofTree.cutRank L hL Γ Δ' T) := by
  subst Δ'
  have hp : htype = rfl := Subsingleton.elim _ _
  cases hp
  rfl

-- ATTACH-BLOCKER: field-notation: dotted helper requires front namespace
theorem G1nnfProofTree.weakenTreeRight_cutRank {L : Language} {hL : L.withoutEquality}
    {Γ Δ : LCS.Finset (FormulaN L)} (T : G1nnfProofTree hL Γ Δ)
    (A : FormulaN L) (hNNF : A.isNNF)
    (hFV : ∀ v, v ∈ formulaFVN A → ¬ T.eigenvariables v) :
    (T.weakenTreeRight A hNNF hFV).cutRank = T.cutRank := by
  induction T with
  | axiom_ rule Γ Δ hAxiom hAC =>
    simp only [G1nnfProofTree.weakenTreeRight]
    let hWeakened :=
      G1nnfRule.applicationConditions_axiom_insert_right
        rule Γ Δ A hAxiom hAC hNNF
    have hSpec := Classical.choose_spec hWeakened
    have hGamma :
        ((Classical.choose hWeakened).conclusion Γ Δ).1 =
          (rule.conclusion Γ Δ).1 := by
      simpa using congrArg Prod.fst hSpec.2.2
    have hDelta :
        ((Classical.choose hWeakened).conclusion Γ Δ).2 =
          LCS.Finset.insert A (rule.conclusion Γ Δ).2 := by
      simpa using congrArg Prod.snd hSpec.2.2
    rw [G1nnfProofTree.cutRank_mp hGamma hDelta]
    rfl
  | onePremise rule Γ Δ hPrem hAC sub ih =>
    cases rule with
    | conjLeft1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | conjLeft2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | disjRight1 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_right
        (LCS.Finset.insert_comm A (.disj B C) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_right
        (LCS.Finset.insert_comm B A Δ) _ _).trans (ih _)
    | disjRight2 B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_right
        (LCS.Finset.insert_comm A (.disj B C) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_right
        (LCS.Finset.insert_comm C A Δ) _ _).trans (ih _)
    | allLeft x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | allRight x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_right
        (LCS.Finset.insert_comm A (.all x B) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_right
        (LCS.Finset.insert_comm
          (formulaSubstN B (.var y) x) A Δ) _ _).trans (ih _)
    | exLeft x B y =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank]
      exact ih _
    | exRight x B t =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_right
        (LCS.Finset.insert_comm A (.ex x B) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank]
      exact (G1nnfProofTree.cutRank_mpr_right
        (LCS.Finset.insert_comm (formulaSubstN B t x) A Δ) _ _).trans
        (ih _)
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | cut _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjRight _ _ => simp [G1nnfRule.premises] at hPrem
    | disjLeft _ _ => simp [G1nnfRule.premises] at hPrem
  | twoPremise rule Γ Δ hPrem hAC sub1 sub2 ih1 ih2 =>
    cases rule with
    | cut B Lam Theta =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_right
        (LCS.Finset.insert_union A Δ Theta) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank, G1nnfRule.cutFormula]
      apply congrArg (fun n => max (B.degree + 1) n)
      exact nat_max_congr
        ((G1nnfProofTree.cutRank_mpr_right
          (LCS.Finset.insert_comm B A Δ) _ _).trans (ih1 _)) rfl
    | conjRight B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises, id]
      refine (G1nnfProofTree.cutRank_mpr_right
        (LCS.Finset.insert_comm A (.conj B C) Δ) _ _).trans ?_
      simp only [G1nnfProofTree.cutRank, G1nnfRule.cutFormula]
      exact nat_max_congr
        ((G1nnfProofTree.cutRank_mpr_right
          (LCS.Finset.insert_comm B A Δ) _ _).trans (ih1 _))
        ((G1nnfProofTree.cutRank_mpr_right
          (LCS.Finset.insert_comm C A Δ) _ _).trans (ih2 _))
    | disjLeft B C =>
      have hp : hPrem = rfl := Subsingleton.elim _ _
      cases hp
      simp only [G1nnfProofTree.weakenTreeRight,
        G1nnfRule.conclusion, G1nnfRule.premises,
        G1nnfProofTree.cutRank, G1nnfRule.cutFormula]
      exact nat_max_congr (ih1 _) (ih2 _)
    | axiomPosAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomNegAtomic _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompLeft _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | axiomCompRight _ _ _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft1 _ _ => simp [G1nnfRule.premises] at hPrem
    | conjLeft2 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight1 _ _ => simp [G1nnfRule.premises] at hPrem
    | disjRight2 _ _ => simp [G1nnfRule.premises] at hPrem
    | allLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | allRight _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exLeft _ _ _ => simp [G1nnfRule.premises] at hPrem
    | exRight _ _ _ => simp [G1nnfRule.premises] at hPrem

end LCS.CutElim.Hauptsatz
end
