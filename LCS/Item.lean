import Lean
-- The project's checklist-item tags are carried by the vendored LeanArchitect
-- `@[blueprint "<id>" (main := true)]` attribute (which replaced the old
-- `@[lcsitem]` / `@[lcsmain]` attributes — see
-- scripts/tools/migrate_lcsitem_to_blueprint.py). Importing `Architect` brings
-- that attribute into scope in every file that imports `LCS.Item`.
import Architect

open Lean

namespace LCS

/-- Look up the blueprint `Node` for `decl`, searching every imported module's
entries. (`blueprintExt.find?` only consults the *current* module's locally
added entries, so in a fully-imported environment we must scan module entries.) -/
def blueprintNode? (decl : Name) (env : Environment) : Option Architect.Node := Id.run do
  for idx in [0 : env.header.moduleNames.size] do
    for (nm, node) in Architect.blueprintExt.getModuleEntries env idx do
      if nm == decl then
        return some node
  return none

/-- Retrieve the checklist item id (the blueprint latex label) for `decl`, if
present. Kept under the historical name `lcsItemId?` so existing tooling that
reads item tags continues to work after the `@[lcsitem]` → `@[blueprint]`
migration. -/
def lcsItemId? (decl : Name) (env : Environment) : Option String :=
  (blueprintNode? decl env).map (·.latexLabel)

/-- True iff `decl` is the MAIN formalization for its item (the blueprint
`main := true` flag). Successor to the old `@[lcsmain]` tag. -/
def isLcsMain (decl : Name) (env : Environment) : Bool :=
  match blueprintNode? decl env with
  | some node => node.main
  | none => false

end LCS
