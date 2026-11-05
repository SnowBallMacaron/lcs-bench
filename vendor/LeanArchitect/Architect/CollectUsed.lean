module

public import Architect.Basic

public meta section

/-!
This is similar to Lean's `collectAxioms`, but collects nodes in the blueprint (plus all axioms)
rather than just axioms.
-/

namespace Architect

open Lean

namespace CollectUsed

structure Context where
  env : Environment
  root : Name

structure State where
  visited : NameSet    := {}
  used    : Array Name := #[]

abbrev M := ReaderT Context $ StateM State

partial def collect (c : Name) : M Unit := do
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM collect
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let { env, root } ← read
    -- When we collect constants used by `a`, we don't just want to return `{a}`.
    if c != root && (blueprintExt.find? env c).isSome then
      modify fun s => { s with used := s.used.push c }
    else
      -- This line is `match env.checked.get.find? c with` in Lean.CollectAxioms
      match env.find? c with
      | some (ConstantInfo.axiomInfo _)  => modify fun s => { s with used := s.used.push c }
      | some (ConstantInfo.defnInfo v)   => collectExpr v.type *> collectExpr v.value
      | some (ConstantInfo.thmInfo v)    => collectExpr v.type *> collectExpr v.value
      | some (ConstantInfo.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
      | some (ConstantInfo.quotInfo _)   => pure ()
      | some (ConstantInfo.ctorInfo v)   => collectExpr v.type
      | some (ConstantInfo.recInfo v)    => collectExpr v.type
      | some (ConstantInfo.inductInfo v) => collectExpr v.type *> v.ctors.forM collect
      | none                             => pure ()

end CollectUsed

/--
Returns the irreflexive transitive set of blueprint nodes that a constant depends on,
as a pair of sets (constants used by type, constants used by value).
They are made disjoint except that possibly both contain `sorryAx`.
-/
def collectUsed [Monad m] [MonadEnv m] [MonadError m] (constName : Name) :
    m (NameSet × NameSet) := do
  let env ← getEnv
  let mut s : CollectUsed.State := {}

  -- Collect constants used by statement
  let info ← getConstInfo constName
  for c in info.type.getUsedConstants do
    (_, s) := ((CollectUsed.collect c).run { env, root := constName }).run s
  let typeUsed := NameSet.ofArray s.used

  -- Collect constants used by proof
  (_, s) := ((CollectUsed.collect constName).run { env, root := constName }).run s
  let valueUsed := NameSet.ofArray s.used

  return (typeUsed, valueUsed \ typeUsed.erase ``sorryAx)

/-!
## See-through dependency collection

The blueprint walk above stops at tagged nodes. For a *raw* declaration
dependency graph (used to build a project's full closure), we instead want to
walk **through** compiler-synthesized helpers (`match_N`, `_sparseCasesOn`,
`brecOn`, `.rec`, `noConfusion`, …) so that an edge that used to route through
such a helper connects the source decl directly to the real target. The
synthesized helpers are never emitted as nodes themselves; their dependencies
are inlined into whatever real declaration referenced them.

This is what makes the resulting graph both **complete** (every real edge is
present, even those that physically pass through a `match` helper) and **free of
false edges** (a synthesized helper shared between two sibling definitions never
manufactures an edge between them, because we follow real dependency edges, not
the helper's *name*).
-/

/-- A declaration that the compiler generated automatically and that should be
seen *through* (never emitted) when building a raw dependency graph:
- internal details (`isInternalDetail`): `_f`, `match_N`, `_sparseCasesOn_N`,
  `_proof_N`, `_eq_N`, `_unsafe_rec`, `_sunfold`, …
- auto-generated recursion principles (`isAuxRecursor`): `brecOn`, `below`,
  `recOn`, `casesOn`, `binductionOn`, …
- `noConfusion` (`isNoConfusion`) and the `.rec` / constructor kernel decls.
- residual inductive boilerplate with no semantic flag: `noConfusionType`,
  `ctorIdx`, `noConfusionType`, `ind`, `sizeOf` (matched by leaf name). -/
def isSyntheticDecl (env : Environment) (n : Name) : Bool :=
  if n.isInternalDetail || isAuxRecursor env n || isNoConfusion env n then
    true
  else
    match env.find? n with
    | some (.recInfo _)  => true   -- `.rec`
    | some (.ctorInfo _) => true   -- constructors
    | _ =>
      match n with
      | .str _ s =>
        -- inductive boilerplate that carries no `ConstantInfo`/aux flag
        [ "noConfusionType", "ctorIdx", "ind", "sizeOf", "binductionOn",
          "rec", "recOn", "casesOn", "brecOn", "below", "noConfusion" ].contains s
      | _ => false

namespace SeeThrough

structure Context where
  env : Environment

structure State where
  visited : NameSet    := {}
  used    : NameSet := {}

abbrev M := ReaderT Context $ StateM State

/-- Walk the dependencies of `c` (a single direction's used-constant set is
seeded by the caller). When a used constant is synthesized, recurse into ITS
used constants (its type + value) instead of recording it; when it is a real
declaration, record it and stop. -/
partial def expand (synthetic : Name) : M Unit := do
  let s ← get
  unless s.visited.contains synthetic do
    modify fun s => { s with visited := s.visited.insert synthetic }
    let { env } ← read
    match env.find? synthetic with
    | none => pure ()
    | some ci =>
      let consts := ci.type.getUsedConstants ++
        (match ci.value? (allowOpaque := true) with
         | some v => v.getUsedConstants
         | none => #[])
      for d in consts do
        if isSyntheticDecl env d then
          expand d
        else
          modify fun s => { s with used := s.used.insert d }

end SeeThrough

/-- See-through raw dependencies of `constName`, returned as
`(typeDeps, valueDeps)` over **real (non-synthesized)** declarations only.
Each set is the result of taking the constant's directly-used constants and, for
every synthesized one, replacing it (recursively) by the real constants it
reaches. `valueDeps` is made disjoint from `typeDeps` (except `sorryAx`),
mirroring `collectUsed`. -/
def collectSeeThrough [Monad m] [MonadEnv m] (constName : Name) :
    m (NameSet × NameSet) := do
  let env ← getEnv
  let run (seeds : Array Name) : NameSet := Id.run do
    let mut st : SeeThrough.State := {}
    for c in seeds do
      if isSyntheticDecl env c then
        (_, st) := ((SeeThrough.expand c).run { env }).run st
      else
        st := { st with used := st.used.insert c }
    return st.used
  match env.find? constName with
  | none => return ({}, {})
  | some ci =>
    let typeSeeds := ci.type.getUsedConstants
    let valueSeeds := match ci.value? (allowOpaque := true) with
      | some v => v.getUsedConstants
      | none => #[]
    let typeDeps := run typeSeeds
    let valueDeps := run valueSeeds
    -- a decl never depends on itself
    let typeDeps := typeDeps.erase constName
    let valueDeps := (valueDeps.erase constName) \ (typeDeps.erase ``sorryAx)
    return (typeDeps, valueDeps)

end Architect
