import LCS.Herbrand.SharpenedHauptsatz.Theorem.SharpenedHauptsatz
import LCS.Herbrand.SharpenedHauptsatz.Theorem.PermutationExample
import LCS.Herbrand.SharpenedHauptsatz.Theorem.MidsequentExample

/-! # Herbrand.SharpenedHauptsatz.Theorem
    Formalization of Chapter 7, Section 3.3: Gentzen's Sharpened Hauptsatz
    for prenex formulae.

    Covers Theorem 7.3.1 (the sharpened Hauptsatz with midsequent)
    and Examples 7.3.3-7.3.4.

    Content modules, in book order:
    - `SharpenedHauptsatz`: Theorem 7.3.1, the midsequent conditions and the
      proof by induction on the measures m(T), n(T).
    - `PermutationExample`: Example 7.3.3.
    - `MidsequentExample`: Example 7.3.4.

    Source: Logic for Computer Science, Gallier 2015

    INDEXED PORT: `FOLKProofTree` is indexed by its conclusion sequent
    (`FOLKProofTree : Sequent L → Type`). Classifier predicates
    (`isStructural`, `isLogical`, `isQuantifier`, …) live on the
    indexed `FOLKStep1` / `FOLKStep2` rule families defined in
    `LCS/Herbrand/SharpenedHauptsatz/Permutability.lean`. No unified
    `FOLKRule` shim is used; each pattern-match destructures directly
    via `.axiom_`, `.onePremise rule t`, `.twoPremise rule t1 t2`.
    WellFormed is built into the indexed type and is not carried as
    a separate conjunct.
-/

namespace LCS.Herbrand.SharpenedHauptsatz.Theorem

end LCS.Herbrand.SharpenedHauptsatz.Theorem
