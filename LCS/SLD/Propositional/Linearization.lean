import LCS.Item
import LCS.Util
import LCS.SLD.SLDForm
import LCS.SLD.SLDForm.Completeness
import LCS.Resolution.Method.FiniteGraph
import Attach
import LCS.SLD.Propositional.Linearization.ProofsStamp

/-! # Linearization of SLD-form proofs (Definition 9.3.1)

Section 9.3.1: the linearization procedure converting a GCNF'-proof in SLD-form into a sequence of negative clauses, with its basic length and nonemptiness facts. -/

section
namespace LCS.SLD.Propositional
open LCS.Resolution.GCNF
open LCS.SLD.SLDForm

-- ========= Definition 9.3.1 (companion): augmentClause =========

/-- Definition 9.3.1 (companion): Adds extra negative literals to a clause
    via set union: C ∪ (Clause.ofList extraLits). Used in the goal splitting
    rule to construct each clause of C'_i by adding neg P_{i+1},...,neg P_n. -/
@[blueprint "chap9__definition_9_3_1"]
def augmentClause (C : Clause) (extraLits : List Literal) : Clause :=
  Clause.union C (Clause.ofList extraLits)

-- ========= Definition 9.3.1 (companion): modifiedSubsequence =========

/-- Definition 9.3.1 (companion): Given a sequence C_i and extra literals,
    drop the last clause from C_i and append the extra literals to each
    remaining clause. Produces C'_i. -/
@[blueprint "chap9__definition_9_3_1"]
def modifiedSubsequence (seq : List Clause) (extraLits : List Literal)
    : List Clause :=
  match seq with
  | [] => []
  | [_] => []  -- drop the last clause
  | c :: rest => augmentClause c extraLits :: modifiedSubsequence rest extraLits

-- ========= Definition 9.3.1: linearize =========

/-- Definition 9.3.1: The noncomputable linearization specification closes every
    trivial label with its complementary pair before inspecting the rule below it.
    Nontrivial nodes follow the binary definite-step/goal-split equations. -/
@[blueprint "chap9__definition_9_3_1" (main := true)]
noncomputable def linearize : {S : ClauseSequent} → GCNFProofTree S → List Clause
  | _, .axiom_ _S _hOrd hTriv =>
    -- Rule (1): axiom neg P, P -> is converted to [{neg P}, Clause.empty]
    -- Extract the negative literal from the axiom. In a well-formed SLD axiom,
    -- S contains {[pos P], [neg P]} for some P. Use the triviality witness.
    let P := Classical.choose hTriv
    [Clause.single (Literal.neg P), Clause.empty]
  | _, .rule Gamma As B _Cs _ _ _hGammaOrd _hAsOrd leftTree rightTree _hNe _hSub _ _ =>
    letI : Decidable (ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B)))) := Classical.propDecidable _
    if hAx : ClauseSequent.isTrivial (Finset.union Gamma (ClauseSequent.mapSet As (fun A => clauseWithLiteral A B))) then
      [Clause.single (Literal.neg (Classical.choose hAx)), Clause.empty]
    else
      match B with
      | Literal.pos P => Clause.single (Literal.neg P) :: linearize leftTree
      | Literal.neg _ =>
        modifiedSubsequence (linearize leftTree) [B] ++ linearize rightTree

end LCS.SLD.Propositional
end
