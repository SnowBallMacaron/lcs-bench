import LCS.Item
import LCS.Util
import LCS.Propositional.Systems.G
import LCS.Propositional.Systems.G.Search
import LCS.Propositional.Systems.G.Search.Fairness
import Attach
import LCS.Propositional.Infinite.Sequents
import LCS.Propositional.Infinite.Semantics.ProofsStamp

/-! # Falsifiable, valid and provable infinite sequents (Definition 3.5.2)
-/
section
namespace LCS.Propositional.Infinite
open LCS.Propositional.Syntax
open LCS.Propositional.Semantics
open LCS.Propositional.Systems.G
open LCS.Propositional.Systems.G.Search

-- ========= Definition 3.5.2: Semantic Notions for Infinite Sequents =========

/-- Definition 3.5.2: A valuation v falsifies an infinite sequent
    Gamma -> Delta if v satisfies every formula A in Gamma (evalExtN v A = T)
    and v falsifies every formula B in Delta (evalExtN v B = F). -/
@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqFalsifies (v : Valuation) (seq : InfSequent) : Prop :=
  (∀ n A, seq.antecedent n = some A → evalExtN v A = BoolVal.T) ∧
  (∀ n B, seq.succedent n = some B → evalExtN v B = BoolVal.F)

/-- Definition 3.5.2: An infinite sequent is falsifiable
    if there exists a valuation that falsifies it. -/

@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqFalsifiable (seq : InfSequent) : Prop :=
  ∃ v : Valuation, infSeqFalsifies v seq

/-- Definition 3.5.2: A valuation v satisfies an infinite
    sequent Gamma -> Delta if, whenever v satisfies every formula A
    in Gamma, then there exists some formula B in Delta such that
    v satisfies B. -/

@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqSatisfies (v : Valuation) (seq : InfSequent) : Prop :=
  (∀ n A, seq.antecedent n = some A → evalExtN v A = BoolVal.T) →
  (∃ n B, seq.succedent n = some B ∧ evalExtN v B = BoolVal.T)

/-- Definition 3.5.2: An infinite sequent is satisfiable
    if there exists a valuation that satisfies it. -/

@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqSatisfiable (seq : InfSequent) : Prop :=
  ∃ v : Valuation, infSeqSatisfies v seq

/-- Definition 3.5.2: An infinite sequent is valid if it
    is satisfied by every valuation. -/

@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqValid (seq : InfSequent) : Prop :=
  ∀ v : Valuation, infSeqSatisfies v seq

/-- Definition 3.5.2: An infinite sequent is provable if
    there exist finite subsequences Gamma_fin of the antecedent and
    Delta_fin of the succedent such that the finite sequent
    Gamma_fin -> Delta_fin is provable in G'. -/

@[blueprint "chap3__definition_3_5_2" (main := true)]
def infSeqProvable (seq : InfSequent) : Prop :=
  ∃ (Gamma_fin : List PropFormulaNormalized) (Delta_fin : List PropFormulaNormalized),
    (∀ A ∈ Gamma_fin, ∃ n, seq.antecedent n = some A) ∧
    (∀ B ∈ Delta_fin, ∃ n, seq.succedent n = some B) ∧
    sequentProvable (Sequent.mk Gamma_fin Delta_fin)

-- ========= Definition 3.5.2 (companion theorem): Provability implies Validity =========

/-- Definition 3.5.2 (companion): If an infinite sequent is provable
    (i.e., there exist finite subsequences of Gamma and Delta forming a
    provable finite sequent), then it is valid (satisfied by every
    valuation). The proof proceeds by extracting the finite witnessing
    sequent, applying finite soundness (Lemma 3.4.3), and lifting the
    result to the infinite sequent. -/
@[blueprint "chap3__definition_3_5_2" (main := true)]
theorem infSeqProvable_implies_valid (seq : InfSequent)
    (h : infSeqProvable seq) : infSeqValid seq 

end LCS.Propositional.Infinite
end
