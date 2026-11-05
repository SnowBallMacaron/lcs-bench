import Lake
open Lake DSL

package LCSLeanCodex5 where
  -- Per-module memory cap (megabytes). Lean aborts the module with "excessive memory consumption
  -- detected" instead of exhausting the host; the largest measured module peaks under 3 GB.
  -- `weakLeanArgs` keeps build traces unchanged, so adding it does not rebuild the book.
  weakLeanArgs := #["-M", "8192"]

-- Private vendored LeanArchitect fork, kept inside the book for Lake sandboxing.
-- Provides the `@[blueprint "id", main := true]` attribute that replaces
-- `@[lcsitem]` / `@[lcsmain]`, plus the patched JSON export (main/leanOk/
-- inferredUses/raw). Pulls in batteries + lean4-cli (pinned v4.35.0).
require LeanArchitect from "vendor/LeanArchitect"

require Attach from "vendor/Attach"

-- Library builds discover imports before ordinary module `needs` run.
-- Await stamps before that discovery; module builds also await the same need.
library_facet attached lib : Unit := do
  discard (← lib.extraDep.fetch).await
  lib.leanArts.fetch

-- Read the registry at build time so registering a front leaves this config constant.
-- Each stamp depends only on its proof text; the aggregate also traces the registry.
target attachedStamps pkg : Unit := do
  let registry ← inputTextFile (pkg.dir / "attached_units.txt")
  let units ← IO.FS.readFile (← registry.await)
  let mut stamps := #[]
  for line in units.splitOn "\n" do
    let unit := line.trimAscii.toString
    if unit.isEmpty then continue
    let dir := pkg.dir / unit.replace "." "/"
    let path := dir / "Proofs.lean"
    let stamp := dir / "ProofsStamp.lean"
    let source ← if ← path.pathExists then inputTextFile path else pure (Job.pure path)
    let job ← buildFileAfterDep stamp source (fun path => do
      let contents ← if ← path.pathExists then IO.FS.readFile path else pure "<missing>"
      IO.FS.createDirAll dir
      IO.FS.writeFile stamp s!"-- Generated from the proof file.\ndef AttachStamp.{unit} : UInt64 := {hash contents}\n")
      (text := true)
    stamps := stamps.push job
  discard (registry.mix (Job.mixArray stamps)).await
  -- Imports carry each stamp's trace. This ordering need must not invalidate
  -- every LCS module when an unrelated proof or registry entry changes.
  return Job.pure ()

@[default_target] lean_lib LCS where
  defaultFacets := #[LeanLib.facetKind ++ `attached]
  needs := #[Lake.PartialBuildKey.mk (.packageTarget .anonymous `attachedStamps)]
