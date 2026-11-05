import LCS.FirstOrder.Gentzen.Part2

section

namespace LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution



proof_of sequentValid_iff_not_falsifiableNoEq := sequentValid_iff_not_falsifiable seq








proof_of soundnessG := by
  -- BEGIN PROOF
    obtain ⟨t⟩ := h
    exact proofTreeValid hL t


end LCS.FirstOrder.Gentzen

end

section

namespace LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

namespace GDeductionTreeExt



helper /-- An extended deduction tree has a non-axiom leaf iff some leaf
    sequent fails to be an axiom. Dual of `isClosed`. Synthetic
    convenience predicate: the textbook uses "nonaxiom leaf" only
    procedurally (grow-left/grow-right) and in the Thm 5.4.1 proof
    narrative ("path to a nonaxiom leaf"), never as a defined term. -/
def GDeductionTreeExt.hasNonaxiomLeaf {L : Language} {s : Sequent L}
    (t : GDeductionTreeExt s) : Prop :=
  ∃ l ∈ t.leaves, ¬ isAxiom l

end GDeductionTreeExt

end LCS.FirstOrder.Gentzen

end

section

namespace LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Basic

open LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Variables

open LCS.FirstOrder.SyntaxN.Substitution

open LCS.FirstOrder.SemanticsN

open LCS.FirstOrder.SemanticsN.Substitution

helper /-- Provability corollary: Over a language without equality, the two
    notions of G-provability coincide.
    Consequently every theorem stated using `sequentProvable` transfers
    to `sequentProvableExt` and vice versa — the §5.4.8 standing
    assumption does not change which sequents are G-provable, only how
    their proofs are organized. Follows from the simulation theorem
    together with its easy converse (every single-term application is
    a k=1 instance of the extended rule). -/
theorem sequentProvable_iff_sequentProvableExt {L : Language} (hL : L.withoutEquality)
    (s : Sequent L) : sequentProvable hL s ↔ sequentProvableExt s := by
-- BEGIN PROOF
  -- DEBT(OD-10: single-term and k-term G-provability coincide over languages without equality, §5.4.8)
  sorry













helper /-- Proof of Lemma 5.4.2 (companion): Over a language without equality,
    an extended one-premise rule preserves and reflects falsifiability in M. -/
theorem ruleFalsificationIff1ExtNoEq {L : Language} (hL : L.withoutEquality)
    (M : Structure L) {prem conc : Sequent L}
    (rule : GentzenStep1ExtNoEq hL prem conc) :
    sequentFalsifiableInNoEq hL M conc ↔ sequentFalsifiableInNoEq hL M prem :=
  ruleFalsificationIff1Ext M rule

helper /-- Proof of Lemma 5.4.2 (companion): Over a language without equality,
    an extended two-premise rule has a conclusion falsifiable in M iff
    at least one premise is falsifiable in M. -/
theorem ruleFalsificationIff2ExtNoEq {L : Language} (hL : L.withoutEquality)
    (M : Structure L) {prem1 prem2 conc : Sequent L}
    (rule : GentzenStep2ExtNoEq hL prem1 prem2 conc) :
    sequentFalsifiableInNoEq hL M conc ↔
    (sequentFalsifiableInNoEq hL M prem1 ∨ sequentFalsifiableInNoEq hL M prem2) :=
  ruleFalsificationIff2Ext M rule

helper /-- Proof of Lemma 5.4.2 (companion): Over a language without equality,
    an extended one-premise rule preserves and reflects validity. -/
theorem ruleValidityIff1ExtNoEq {L : Language} (hL : L.withoutEquality)
    {prem conc : Sequent L} (rule : GentzenStep1ExtNoEq hL prem conc) :
    sequentValidNoEq hL conc ↔ sequentValidNoEq hL prem :=
  ruleValidityIff1Ext rule

helper /-- Proof of Lemma 5.4.2 (companion): Over a language without equality,
    an extended two-premise rule has a valid conclusion iff both premises
    are valid. -/
theorem ruleValidityIff2ExtNoEq {L : Language} (hL : L.withoutEquality)
    {prem1 prem2 conc : Sequent L} (rule : GentzenStep2ExtNoEq hL prem1 prem2 conc) :
    sequentValidNoEq hL conc ↔ (sequentValidNoEq hL prem1 ∧ sequentValidNoEq hL prem2) :=
  ruleValidityIff2Ext rule

helper /-- Proof of Lemma 5.4.3 (companion): Over a language without equality,
    every proof tree using the §5.4.8 extended rules has a valid conclusion. -/
theorem proofTreeValid_ExtNoEq {L : Language} (hL : L.withoutEquality)
    {s : Sequent L} (t : GProofTreeExtNoEq hL s) : sequentValidNoEq hL s :=
  proofTreeValid_Ext t

helper /-- Proof of Lemma 5.4.3 (companion): Over a language without equality,
    provability using the §5.4.8 extended rules implies validity. -/
theorem soundnessG_ExtNoEq {L : Language} (hL : L.withoutEquality)
    (seq : SequentNoEq L hL) (h : sequentProvableExtNoEq hL seq) :
    sequentValidNoEq hL seq :=
  soundnessG_Ext seq h



end LCS.FirstOrder.Gentzen

end

section

namespace LCS.FirstOrder.Gentzen

open LCS.FirstOrder.Basic LCS.FirstOrder.SyntaxN

open LCS.FirstOrder.SyntaxN.Substitution

helper /-- The listed substitutions are removed by exactly one ∀:left step per term. -/
theorem allLeft_singleTermChain {L : Language} (hL : L.withoutEquality)
    (ts : List (Term L)) (Γ Δ Λ : List (FormulaN L)) (x : Nat) (A : FormulaN L)
    (hfree : ∀ t ∈ ts, isFreeForN t x A) :
    ∃ tree : GDeductionTree hL (.mk (Γ ++ [.all x A] ++ Δ) Λ),
      tree.QuantifierChain hL
        (.mk (Γ ++ ts.map (fun t => formulaSubstN A t x) ++ [.all x A] ++ Δ) Λ)
        false ts.length := by
  induction ts generalizing Γ with
  | nil => exact ⟨.leaf _, by simpa only [List.map_nil, List.append_nil, List.length_nil] using (GDeductionTree.QuantifierChain.leaf (hL := hL)
      (prem := Sequent.mk (Γ ++ [.all x A] ++ Δ) Λ) false)⟩
  | cons t ts ih =>
      have hrec := ih (Γ ++ [formulaSubstN A t x])
        (fun u hu => hfree u (List.mem_cons_of_mem t hu))
      rw [List.append_assoc Γ [formulaSubstN A t x] [FormulaN.all x A]] at hrec
      have hrec' : ∃ tree : GDeductionTree hL
          (.mk (Γ ++ [formulaSubstN A t x, .all x A] ++ Δ) Λ),
          tree.QuantifierChain hL
            (.mk (Γ ++ (t :: ts).map (fun u => formulaSubstN A u x) ++ [.all x A] ++ Δ) Λ)
            false ts.length := by
        simpa only [List.map_cons, List.append_assoc, List.singleton_append,
          List.cons_append, List.nil_append] using hrec
      obtain ⟨tree, htree⟩ := hrec'
      have ht := hfree t (List.mem_cons_self ..)
      exact ⟨.onePremise (.allLeft t Γ Δ Λ x A ht) tree,
        .allLeft t Γ Δ Λ x A ht htree⟩

helper /-- The listed substitutions are removed by exactly one ∃:right step per term. -/
theorem exRight_singleTermChain {L : Language} (hL : L.withoutEquality)
    (ts : List (Term L)) (Γ Δ Λ : List (FormulaN L)) (x : Nat) (A : FormulaN L)
    (hfree : ∀ t ∈ ts, isFreeForN t x A) :
    ∃ tree : GDeductionTree hL (.mk Γ (Δ ++ [.ex x A] ++ Λ)),
      tree.QuantifierChain hL
        (.mk Γ (Δ ++ ts.map (fun t => formulaSubstN A t x) ++ [.ex x A] ++ Λ))
        true ts.length := by
  induction ts generalizing Δ with
  | nil => exact ⟨.leaf _, by simpa only [List.map_nil, List.append_nil, List.length_nil] using (GDeductionTree.QuantifierChain.leaf (hL := hL)
      (prem := Sequent.mk Γ (Δ ++ [.ex x A] ++ Λ)) true)⟩
  | cons t ts ih =>
      have hrec := ih (Δ ++ [formulaSubstN A t x])
        (fun u hu => hfree u (List.mem_cons_of_mem t hu))
      rw [List.append_assoc Δ [formulaSubstN A t x] [FormulaN.ex x A]] at hrec
      have hrec' : ∃ tree : GDeductionTree hL
          (.mk Γ (Δ ++ [formulaSubstN A t x, .ex x A] ++ Λ)),
          tree.QuantifierChain hL
            (.mk Γ (Δ ++ (t :: ts).map (fun u => formulaSubstN A u x) ++ [.ex x A] ++ Λ))
            true ts.length := by
        simpa only [List.map_cons, List.append_assoc, List.singleton_append,
          List.cons_append, List.nil_append] using hrec
      obtain ⟨tree, htree⟩ := hrec'
      have ht := hfree t (List.mem_cons_self ..)
      exact ⟨.onePremise (.exRight t Γ Δ Λ x A ht) tree,
        .exRight t Γ Δ Λ x A ht htree⟩

proof_of ExtendedAllLeft.simulateInference := by
  cases rule with
  | mk ts Γ Δ Λ x A hne hfree => exact allLeft_singleTermChain hL ts Γ Δ Λ x A hfree


proof_of ExtendedExRight.simulateInference := by
  cases rule with
  | mk ts Γ Δ Λ x A hne hfree => exact exRight_singleTermChain hL ts Γ Δ Λ x A hfree


end LCS.FirstOrder.Gentzen

end
