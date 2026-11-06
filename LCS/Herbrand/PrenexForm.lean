import LCS.Herbrand.PrenexForm.PrenexFormulas
import LCS.Herbrand.PrenexForm.Equivalences
import LCS.Herbrand.PrenexForm.PrenexNormalForm
import LCS.Herbrand.PrenexForm.Example
import LCS.Herbrand.PrenexForm.DisjunctiveNormalForm

/-! # Herbrand.PrenexForm
    Formalization of Chapter 7, Section 2: Prenex Normal Form.

    Covers Definition 7.2.1 (prenex form), Lemma 7.2.1 (quantifier
    equivalences), Theorem 7.2.1 (prenex normal form existence),
    Example 7.2.1 (step-by-step prenex conversion),
    and Lemma 7.2.2 (disjunctive normal form for quantifier-free formulae).

    Content modules, in book order:
    - `PrenexFormulas`: Definition 7.2.1.
    - `Equivalences`: Lemma 7.2.1.
    - `PrenexNormalForm`: Theorem 7.2.1, by induction on the formula and as a
      conversion function.
    - `Example`: Example 7.2.1.
    - `DisjunctiveNormalForm`: Lemma 7.2.2.

    Source: Logic for Computer Science, Gallier 2015
-/

namespace LCS.Herbrand.PrenexForm

end LCS.Herbrand.PrenexForm
