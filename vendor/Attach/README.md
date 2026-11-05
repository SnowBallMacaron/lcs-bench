# Attach

Vendored from `${HOME}/workspace/_scratch/front-layout-demo`, master commit
`2544c514483c802054676374c1965cd7dd2ffb6b`. `Attach.lean` and every
`Attach/*.lean` file (currently `Parser.lean` and `Shadow.lean`) are verbatim
copies; future syncs overwrite these files.
Pinned to `leanprover/lean4:v4.35.0`, matching this book.

A front imports `Attach`, its ordinary dependencies (including
`Architect.Attribute` for blueprint tags), and `<Unit>.ProofsStamp`. It owns
statements and context, declaring bodiless theorems such as
`@[blueprint "smoke__t" (main := true)] theorem t (n : Nat) : n = n`.
`<Unit>/Proofs.lean` imports the front and supplies `proof_of t := by rfl` in
the matching namespace. Proof files may contain `namespace`, `end`, `section`, `open`, and
`helper theorem|def|structure|inductive|abbrev` declarations. Missing or failing proofs emit
positioned warnings and insert `sorry`; `set_option attach.strict true` makes
these failures errors. Use `#print axioms` to audit attached declarations.

## Proof-file grammar and isolation

Theorem and def helpers accept plain `@[simp]`, rewritten to `@[scoped simp]`
in `<Unit>.Proofs`, including helpers with namespace-qualified names. Attributes
are applied from this root after declaration elaboration. Helpers and proof blocks activate this scope locally;
front declarations and consumers do not. Consumers may opt in with
`open scoped <Unit>.Proofs`. Explicit local/scoped simp attributes, priorities,
other simp modifiers, and all other helper attributes are rejected. Structure,
inductive, and abbrev helpers accept no attributes. Generated constructors,
projections, and recursors remain under the helper name; helper elaboration
sets `genSizeOf = false` to avoid automatic instance registration.

Private and root-qualified helpers, classes, instances, ordinary unwrapped
declarations, notation, macros, syntax extensions, attribute commands,
top-level options/variables, mutual blocks, and executable commands are rejected.
Helper `deriving` clauses and nested `run_tac` / `by_elab` syntax in helpers or
proof blocks are hard errors, including with strict mode disabled. Dependencies
must already be imported by the front; proof imports are consumed during loading.

Before loading proofs, the shadow pass re-elaborates the complete front from
its import-only environment with placeholders for attached theorem bodies.
It compares declaration types and universe parameters, definition/opaque values,
and generated inductive/recursor metadata. Theorem proof terms may differ, but
attached theorems, kept front theorems and proof-window theorem realizations
undergo an axiom check. Standard axioms `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Attached proofs may reuse axioms from the front's original import closure,
including imported native-decide lemmas. They may also reuse native evidence
from a kept declaration whose type/value comparison passes and whose original
compiled body already uses the native-decide axiom family. Attached proofs and
proof-file helpers cannot introduce their own native axioms.
For kept theorems and verified realizations, other imported axioms still require
an original dependency; the `Lean.ofReduceBool` / generated `native_decide`
or `decide +native`
family requires an original use of that family. Unrelated local axioms remain
errors. Proof-file imports and additions do not extend the saved import closure.

Direct missing/sorry attached proofs and their native auxiliaries are tracked
as incomplete work. Attach emits one grouped `attached proof of X is incomplete
(sorry)` warning, listing dependents that inherit `sorryAx`; strict mode makes
it an error. New sorry in statements, helpers, kept bodies or counterfeit
realizations remains a hard error. A successful non-strict build with an
incomplete-proof warning is not a completed proof. Existing sorry dependencies
from the front's original import closure are inherited debt and pass this check;
unchanged direct debt in kept front declarations is also permitted only when
both the compiled type and body match exactly. New direct sorries and proof-file
helper sorries still fail strict checking.
The splitter separately verifies that each tagged declaration's axiom set agrees
with its pre-split snapshot.

Generated auxiliaries must lack both exported and server declaration ranges.
Every component after the longest existing owner must be a known Lean generator
kind with decimal indices of any depth, a splitter, a registered reserved-name
link, or have native auxiliary metadata. Known kinds are `match`, `_match`,
`proof`, `eq`, `_eq`, `_proof`, `_simp`, `_sparseCasesOn`, and `_auxLemma`.
Arbitrary numbered names alone do not qualify. Stable products `_default`,
`_unsafe_rec`, `_f`, `_unary`, `_mutual`, and `_sizeOf_*` retain comparison.
Under an attached theorem owner, a theorem-valued `_unary` with Lean's native
recursion tag is proof-local; the name alone grants no exception. Kept owners
still compare their stable products.
References to generated definitions normalize recursively; generated theorem
references compare by their statement types. Source declarations retain their
range-based identity regardless of spelling.

Attach records declarations created during helper/proof elaboration, including
reserved-name realizations. These must match Lean's own realization even when
the shadow already contains the name. Beneath attached theorems, additions
require native auxiliary, matcher, sparse-helper, recursion, or source-range
metadata. Helpers under `<Unit>.Proofs` remain exempt. Unrelated declarations
or changed types/values report `proof file changed its elaboration` as hard errors.

Shadow elaboration reuses imports. Verification of a window-created name with
an imported owner lazily allocates an independent import realization environment,
at most once per check. Owner search stops at local declarations, even under
an imported namespace such as `Nat`. Local owners pay no import-isolation cost.
Moving a global simp helper can therefore expose a front declaration that
implicitly depended on it.

After each helper or proof block, Attach checks instance registrations, scoped
activation state, and parser state. Helper isolation failure restores the entire
pre-helper environment, removes its declarations, reports a positioned hard
error, and marks the helper done. Following blocks are skipped with warnings
and `sorry`; later front statements use the restored environment. A block
isolation failure also restores its saved state before inserting `sorry` and
reporting a hard error. The loader restores its environment after collecting
saved helpers and blocks, including unwinding unclosed namespaces and scopes.
Imported elaborators remain trusted code; these checks are not a sandbox.

The prototype's complete contract suite at revision `2544c51` reports 150/150 contract
tests and 26/26 acceptance checks. Its `lakefile.lean` is unchanged since the previously vendored commit
`b7306c31793e8abd1f0612744d9e5a80155a4aed` (recorded at book commit
`675ee2af1`), so this sync needs no new Lake options or stamp configuration.

## Book build integration

List fully qualified front module names in the book's `attached_units.txt`,
one per line, sorted and newline-terminated. `lake exe attach_split --write
<Unit> --lakefile` updates this registry. The single `attachedStamps` target
reads it at build time through a traced `inputTextFile`; registration leaves
`lakefile.lean` and its compiled configuration unchanged. Each conventional
`<Unit>/Proofs.lean` is independently traced and produces a content-hash
`ProofsStamp.lean` through `buildFileAfterDep`. Missing proof files use the text
`<missing>` for their hash. Commit the registry and generated stamps with a new
front; `.hash` / `.trace` files and `.lake` products are build artifacts.
Do not add proof files as library roots.

The existing `LCS` library uses the `attached` default facet, which awaits
`lib.extraDep` before calling `lib.leanArts.fetch` and discovering module imports.
Its `needs` names `attachedStamps`, covering direct module builds as well.
No separate LCS library is created and the existing roots/globs are retained.
An empty registry creates no stamp files or changed module inputs.

After editing a proof file, run
`lake build LCS.Propositional.Semantics` for that registered front. **No separate
refresh command is required:** the proof input trace changes the stamp, whose
import rebuilds the front. A proof-only comment edit also triggers rebuilding.
Use library/module targets; explicitly requesting internal library facets can
bypass the initial ordering. Editor sessions may require reload after building.
A custom `attach.proofFile` path also requires corresponding input tracking.

## Integration smoke test (2026-10-17)

A temporary `AttachSmoke` library outside LCS used the same facet and `needs`,
with `AttachSmoke` registered in the units list, a front importing its stamp, the blueprint
theorem above, and a proof file containing `proof_of t := by` followed by `rfl`.
The stamp did not exist before the first library build. The temporary source,
stamp, and library registration were removed after testing; this report retains
the results. No LCS source files were edited.

- `lake build Attach`: passed, 2.65 s.
- `lake build AttachSmoke`: passed, 3.49 s; `#print axioms AttachSmoke.t`
  reported that it does not depend on any axioms.
- Append a proof-only comment, then `lake build +AttachSmoke`: passed, 1.25 s.
  Lake rebuilt the stamp target, stamp module, and front; axioms remained empty.
- Replace `rfl` with `exact True.intro`, then `lake build AttachSmoke`: passed
  with the intended warning/sorry fallback, 1.14 s. Diagnostic payload:

  ```text
  AttachSmoke/Proofs.lean:4:2: Type mismatch
    True.intro
  has type
    True
  but is expected to have type
    n = n
  ```

  Lake's outer location was `AttachSmoke.lean:4:2`; the payload preserved the
  actual proof-file location. It also warned ``declaration uses `sorry` `` at
  `AttachSmoke.lean:5:47`, and the axiom audit reported `[sorryAx]`.

- With the unit list empty again, `lake build LCS.Propositional.Semantics`
  passed in 11.98 s (building dependencies); a repeat passed in 0.52 s with
  no compilation jobs, only replayed existing warnings. No stamp sources remain.
- `lake build` after smoke removal: 84.91 s, failed only on the known roots
  `LCS.SLD.SLDForm`, `LCS.FOResolution.GroundResolution`, and
  `LCS.Herbrand.SHGTheorem.Herbrand`. These failures were left unchanged.
- A final cached `lake build Attach` passed in 0.50 s without dependency fetches.

The first commit hook attempt failed before building: its exported Git worktree
variables leaked into Lake dependency Git operations. That attempt changed the
repository's origin URL; it was restored to its prior value. Retrying with a
temporary Lake wrapper that unsets `GIT_DIR` and `GIT_WORK_TREE` ran the full
hook build in 17.03 s and failed only on the same three known roots above.
The commit therefore used the authorized `--no-verify` exception. The wrapper
is not part of the repository.

## Split-unit validation (2026-10-18)

Revision `6f5b822` builds as the Attach library, but its shadow pass rejects
generated equation/matcher declarations in both Semantics and NormalForms.
The split-unit verifiers and chapter 3 build therefore fail. The splitter
suite passes 30/33 tests; chapter 3/4 mistag counts remain zero using largely
stale index records. Both split units verify and chapter 3 builds with the
previous Attach revision. See [the split validation report](../../docs/attach-split.md#attach-sync-validation-2026-10-18)
for the regeneration procedure, failure details, and index freshness counts.

Re-sync `86a7a62` accepts these realizations: both fronts and Proofs modules
build with zero shadow errors, both unit verifiers pass, and the splitter suite
passes 33/33 tests. See [the re-sync results](../../docs/attach-split.md#attach-re-sync-2026-10-18-prototype-86a7a62)
for chapter 3 build and index/lint counts.

## Proof-file diagnostic identity (c4ed04b)

Helper/proof info trees keep their proof-file source identity. Command linters
run with that file's context; foreign info trees are kept out of front-command
linters. Deferred proof diagnostics run after the attached declaration exists.
This fixes the cross-file UTF-8 boundary panic in diagnostic suggestions.
Sources above were copied from committed blobs, excluding later uncommitted
prototype development.

Topic fronts created by the module splitter may use
`attach_helper_namespace Parent.Unit.Proofs` after imports. The namespace must
be an ancestor unit's reserved `Proofs` namespace. This persistent mapping keeps
helper declarations and scoped simp entries under their original names when a
front/proof unit is divided into topic units; standalone checks recover it from
the compiled owner module. Proof files retain the existing restricted grammar.

The current automated smoke fixture is
`tests/fixtures/attach_split/AttachSmoke.lean`. The writer integration test
registers it through `attached_units.txt` and checks proof edits, selective
stamp updates, missing inputs, an empty registry, and constant configuration
mtime. The measurements above describe the original 2026-10-17 run.
