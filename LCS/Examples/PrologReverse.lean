import LCS.Item
import LCS.Util
import LCS.FirstOrder.SemanticsN
import LCS.FOResolution.Unification
import LCS.FOResolution.Method.Soundness
import LCS.SLD.FirstOrder
import LCS.SLD.PrologSyntax
import LCS.SLD.LogicProgramming
import LCS.SLD.LogicProgramming.Correctness
import LCS.Examples.PrologReverse.Program
import LCS.Examples.PrologReverse.Refutation

set_option linter.unusedSimpArgs false

/-! # Examples.PrologReverse — verified Prolog `reverse/2` via `append/3`

    A classic Prolog program: list reversal expressed via the
    "naive reverse" definition on top of `append/3`.

    ```prolog
    % Program:
    append([],       L, L).
    append([X | Xs], Y, [X | Zs]) :- append(Xs, Y, Zs).

    reverse([], []).
    reverse([H | T], R) :- reverse(T, Rt), append(Rt, [H], R).

    % Query:
    ?- reverse([a, b], R).

    % Expected answer:
    R = [b, a].
    ```

    The novel feature relative to `PrologAppend` / `PrologMember`:
    * The program has **two predicates** (`append/3` and `reverse/2`)
      that call each other — this is **nontrivial Prolog**, not just a
      flat single-predicate family.
    * A single refutation threads both predicates: the recursive
      reverse clause unfolds into one `reverse` sub-goal AND one
      `append` sub-goal; the sub-goals in turn unfold via their own
      clauses until everything collapses to `[]`.
    * Variables are introduced at each unfolding and threaded through
      the final composed substitution, so the answer `R = [b, a]` is
      a non-trivial result of composing many σ-steps.

    The full 6-step refutation is assembled as a chain of
    `FOSLDDerivation.init` / `FOSLDDerivation.step` applications,
    following the same pattern as `PrologAppend.appendSLDStep1`
    / `appendSLDRefutation` but at larger scale. All constructor
    side conditions (hMGU, hSep, hStdApart, hAk, hHead) are fully
    discharged via the §2b / §4b helper lemmas; no sorry anywhere
    in the derivation chain. `revRefutation_exists` is a real
    `⟨[], revSLDRefutation, rfl⟩`, and the end-to-end semantic lift
    feeds the concrete refutation directly into Lemma 9.5.3. -/

namespace LCS.Examples.PrologReverse

open LCS.FirstOrder.Basic
open LCS.FirstOrder.SyntaxN
open LCS.FirstOrder.SemanticsN
open LCS.FOResolution.Unification
open LCS.FOResolution.ClauseForm
open LCS.FOResolution.Method
open LCS.FOResolution.Method.Soundness
open LCS.SLD.FirstOrder
open LCS.SLD.PrologSyntax
open LCS.SLD.LogicProgramming
open LCS.SLD.LogicProgramming.Correctness

-- ===================================================================
-- §1.  Language L_rev = { constants a, b, []; function ./2;
--                         predicates append/3, reverse/2 }
-- ===================================================================


end LCS.Examples.PrologReverse
