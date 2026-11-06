import LCS.Item
import LCS.Util
import LCS.FirstOrder.Basic
import LCS.FirstOrder.Syntax.Substitution
import LCS.FirstOrder.Syntax.Variables
import LCS.FirstOrder.SyntaxN
import LCS.FirstOrder.SyntaxN.Variables
import LCS.FirstOrder.SyntaxN.Substitution
import LCS.FirstOrder.SemanticsN
import LCS.FirstOrder.Semantics.Substitution
import LCS.Propositional.Syntax
import LCS.Propositional.Semantics
import LCS.FirstOrder.Semantics.Subformulae.RectifiedFormulae
import LCS.FirstOrder.Semantics.Subformulae.RenamingBoundVariables
import LCS.FirstOrder.Semantics.Subformulae.Rectification
import LCS.FirstOrder.Semantics.Subformulae.SubstitutionInTautologies

/-! # FirstOrder.Semantics.Subformulae
    Formalization of Chapter 5, Sections 5.3.6-5.3.7.
    Subformulae, rectified formulae, and valid formulae from tautologies.

    Content modules, in book order:
    - `Subformulae.RectifiedFormulae` — Section 5.3.6, Definitions 5.3.9-5.3.10 (subformulae, binding quantifiers, rectified formulae)
    - `Subformulae.RenamingBoundVariables` — Section 5.3.6, Lemma 5.3.4 (i) (renaming a bound variable preserves meaning)
    - `Subformulae.Rectification` — Section 5.3.6, Lemma 5.3.4 (ii) (rectification algorithm) and Example 5.3.3
    - `Subformulae.SubstitutionInTautologies` — Section 5.3.7, Definition 5.3.11, Example 5.3.4, Lemma 5.3.5 (valid formulae obtained by substitution in tautologies)
-/

namespace LCS.FirstOrder.Semantics.Subformulae

end LCS.FirstOrder.Semantics.Subformulae
