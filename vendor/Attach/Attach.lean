import Attach.Parser
import Attach.Shadow

open Lean Elab Command Meta Tactic

register_option attach.proofFile : String := {
  defValue := "", descr := "Attached proof file (relative to the working directory)"
}
register_option attach.strict : Bool := {
  defValue := false, descr := "Reject missing and failing attached proofs"
}

namespace Attach

structure Record where
  name : Name
  path : String
  locals : List Name
  deriving Inhabited
initialize records : SimplePersistentEnvExtension Record (NameMap Record) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s r => s.insert r.name r
    addImportedFn := fun arrays => arrays.foldl (fun s rs =>
      rs.foldl (fun s r => s.insert r.name r) s) {}
  }
structure Saved where
  stx : Syntax
  path : String
  fileMap : FileMap
  scope : Scope
  activeScopes : List Name
  deriving Inhabited
structure Block extends Saved where
  helperCount : Nat
structure ProofLint extends Saved where
  info : InfoState
  messages : MessageLog
structure Cache where
  shadow : Option Shadow.Snapshot := none
  proofConstants : NameSet := {}
  including : Bool := false
  loaded : List String := []
  blocks : NameMap Block := {}
  helpers : Array Saved := #[]
  done : Nat := 0
  failedHelper : Option Nat := none
  used : NameSet := {}
  proofLints : Array ProofLint := #[]
  deriving Inhabited
private initialize cache : EnvExtension Cache ← registerEnvExtension (pure {})

-- Track every new constant, including realizeConst results whose extension
-- state comes from their owner's saved environment rather than this window.
private def withProofWindow (action : CommandElabM Unit) : CommandElabM Unit := do
  let before ← getEnv
  try
    action
  finally
    let after ← getEnv
    let added : NameSet := after.constants.foldStage2 (s := {}) fun names n _ =>
      if before.constants.contains n then names else names.insert n
    modifyEnv fun env => cache.modifyState env fun s => { s with
      proofConstants := added.toList.foldl (fun ns n => ns.insert n) s.proofConstants }

private def activeScopes (env : Environment) : List Name :=
  match (Parser.parserExtension.ext.getState env).stateStack with
  | s :: _ => s.activeScopes.toList
  | [] => []

-- Parser states contain closures, so structural equality is unavailable. Scope
-- pop preserves the original immutable state objects; identity is conservative.
private unsafe def sameObjectImpl (a b : α) : Bool := ptrEq a b
@[implemented_by sameObjectImpl]
private opaque sameObject {α : Type u} (a b : α) : Bool

private def isolationChanges (before : Environment) : CoreM (List String) := do
  let after ← getEnv
  let mut changes := []
  for ext in (← scopedEnvExtensionsRef.get) do
    let a := (ext.ext.getState before).stateStack
    let b := (ext.ext.getState after).stateStack
    unless a.map (fun s => (s.activeScopes.toList, s.delimitsLocal)) ==
        b.map (fun s => (s.activeScopes.toList, s.delimitsLocal)) do
      changes := changes ++ [s!"proof-file isolation: scoped-extension activation state changed ({ext.descr.name})"]
  let a := instanceExtension.ext.getState before
  let b := instanceExtension.ext.getState after
  unless (a.stateStack.length == b.stateStack.length &&
      (a.stateStack.zip b.stateStack).all (fun (x, y) => sameObject x.state y.state)) &&
      sameObject a.newEntries b.newEntries && sameObject a.scopedEntries b.scopedEntries do
    changes := changes ++ ["proof-file isolation: instance table changed"]
  let a := Parser.parserExtension.ext.getState before
  let b := Parser.parserExtension.ext.getState after
  unless (a.stateStack.length == b.stateStack.length &&
      (a.stateStack.zip b.stateStack).all (fun (x, y) => sameObject x.state y.state)) &&
      sameObject a.newEntries b.newEntries && sameObject a.scopedEntries b.scopedEntries do
    changes := changes ++ ["proof-file isolation: parser state changed"]
  return changes

private def withProofScope (scopes : List Name) (action : CommandElabM Unit) : CommandElabM Unit := do
  Lean.pushScope
  try
    for ns in scopes do Lean.activateScoped ns
    action
  finally
    Lean.popScope

private def save (stx : Syntax) : CommandElabM Saved := do
  return ⟨stx, (← read).fileName, (← read).fileMap, ← getScope, activeScopes (← getEnv)⟩
private def strict : CoreM Bool := do
  return attach.strict.get (← getOptions) || (← IO.getEnv "ATTACH_STRICT") == some "1"
private def locatedMessages (path : String) (messages : MessageLog) : MessageLog :=
  { messages with unreported := messages.unreported.map fun msg =>
    if msg.fileName == path && !msg.data.hasTag (· == `Attach.located) then
      { msg with data := .tagged `Attach.located (m!"{path}:{msg.pos.line}:{msg.pos.column}: {msg.data}") }
    else msg }
private def retainLocations (path : String) : CoreM Unit := do
  Core.setMessageLog (locatedMessages path (← Core.getMessageLog))
private partial def hasAtom (stx : Syntax) (text : String) : Bool :=
  stx.isAtom && stx.getAtomVal == text || stx.getArgs.any (hasAtom · text)
private partial def firstAtom (stx : Syntax) : String :=
  if stx.isOfKind ``Parser.Command.declaration then firstAtom stx[1]
  else if stx.isAtom then stx.getAtomVal else
    (stx.getArgs.toList.map firstAtom |>.find? (!·.isEmpty)).getD ""

-- Inspect the entire syntax tree, including nested terms and tactic sequences.
private partial def rejectMetaprogramming (stx : Syntax) : CoreM Unit := do
  let construct := if stx.isOfKind ``Lean.byElab || stx.isOfKind `Lean.Parser.Term.byElab then "by_elab"
    else if stx.isOfKind ``Parser.Tactic.runTac then "run_tac" else ""
  unless construct.isEmpty do
    throwErrorAt stx (MessageData.tagged `Attach.forbiddenSyntax
      m!"{construct} is forbidden in proof files")
  for arg in stx.getArgs do rejectMetaprogramming arg

private def validateHelper (cmd : Syntax) : CommandElabM Unit := do
  if hasAtom cmd "private" then throwErrorAt cmd "private is forbidden in proof files"
  let valueHelper := cmd[1].isOfKind ``Parser.Command.theorem ||
    cmd[1].isOfKind ``Parser.Command.definition
  unless cmd.isOfKind ``Parser.Command.declaration &&
      (valueHelper || cmd[1].isOfKind ``Parser.Command.abbrev ||
       cmd[1].isOfKind ``Parser.Command.inductive ||
       (cmd[1].isOfKind ``Parser.Command.structure &&
        cmd[1][0].isOfKind ``Parser.Command.structureTk)) do
    throwErrorAt cmd "unsupported proof-file command helper {firstAtom cmd}; use helper theorem or helper def, structure, inductive, abbrev"
  liftCoreM (rejectMetaprogramming cmd)
  if hasAtom cmd "deriving" then
    throwErrorAt cmd "deriving is forbidden on helper {cmd[1][1][0]}"
  for attr in cmd[0][1][0][1].getSepArgs do
    let stx := attr[1]
    let name := if stx.isOfKind ``Parser.Attr.simple then stx[0].getId.eraseMacroScopes
      else Name.mkSimple stx.getKind.getString!
    unless valueHelper && stx.isOfKind ``Parser.Attr.simp && attr[0][0].getArgs.isEmpty &&
        (stx.getArgs.extract 1 stx.getArgs.size).all (·.getArgs.isEmpty) do
      throwErrorAt attr "forbidden helper attribute {name} on helper {cmd[1][1][0]}; only plain @[simp] is allowed"
  -- Root-qualified names would escape the reserved namespace.
  if (`_root_).isPrefixOf cmd[1][1][0].getId then
    throwErrorAt cmd "helper names must stay in the reserved Proofs namespace"

-- Qualified declaration elaboration temporarily enters the declaration's child
-- namespace. Apply the accepted attributes afterwards, from the helper root,
-- so all helper simp entries share the scope that proofs and consumers open.
private def elabHelper (cmd : Syntax) : CommandElabM Unit :=
  withScope (fun s => { s with opts := s.opts.setBool `genSizeOf false }) do
    withProofScope [← getCurrNamespace] do
      let attrs ← elabAttrs cmd[0][1][0][1].getSepArgs
      let name := (← getCurrNamespace) ++ cmd[1][1][0].getId
      elabCommand (cmd.setArg 0 (cmd[0].setArg 1 mkNullNode))
      unless attrs.isEmpty do
        liftTermElabM <| Term.applyAttributes name (attrs.map fun attr => { attr with kind := .scoped })

elab_rules : command
  | `(helper $cmd:command) => do
    validateHelper cmd
    if (cache.getState (← getEnv)).including then
      let saved ← save cmd
      modifyEnv fun env => cache.modifyState env fun s => { s with helpers := s.helpers.push saved }
    else
      -- Writer helper names are relative to one shared root, just as in
      -- runHelpers. A source-namespace-specific check root loses earlier
      -- parent helpers when a later declaration enters a child namespace.
      let checkRoot := (← getEnv).mainModule ++ `_attachCheck
      withScope (fun s => { s with
          currNamespace := checkRoot
          openDecls := .simple s.currNamespace [] :: s.openDecls }) do
        elabHelper cmd

elab "attached_type% " id:ident : term => return (← getConstInfo id.getId).type
elab "attach_replay " id:ident " => " tacs:tacticSeq : tactic => do
  let some r := (records.getState (← getEnv)).find? id.getId
    | throwError "no attached binder record for {id}"
  let (_, goal) ← (← getMainGoal).introN r.locals.length r.locals
  replaceMainGoal [goal]
  evalTactic tacs

private def parseBody (b : Block) : CoreM (TSyntax `term) := do
  let source := (b.fileMap.source.toRawSubstring.extract 0 (b.stx.getTailPos?.getD 0)).toString
  let input := Parser.mkInputContext source b.path
  let p := Parser.andthenFn Parser.whitespace (Parser.categoryParserFn `term)
  let ps := p.run input { env := ← getEnv, options := ← getOptions }
    (Parser.getTokenTable (← getEnv)) { Parser.mkParserState source with pos := (b.stx.getPos?.getD 0) }
  let rest := input.extract ps.pos input.endPos
  if rest.startsWith "termination_by" || rest.startsWith "decreasing_by" then
    throwError (MessageData.tagged `Attach.unsupportedSuffix
      m!"termination_by on attached theorems is unsupported (including decreasing_by)")
  if !ps.allErrors.isEmpty then throwError "{ps.toErrorMsg input}"
  if !input.atEnd ps.pos then throwError "{(ps.mkError "end of proof block").toErrorMsg input}"
  rejectMetaprogramming ps.stxStack.back
  return ⟨ps.stxStack.back⟩

-- Command linters may ignore a tree's context and use the ambient fileMap.
-- Run them here, then prevent foreign trees from reaching the front's linters.
private def lintProofTrees (stx : Syntax) (info : InfoState) : CommandElabM Unit := withRef stx do
  setInfoState info.substituteLazy.get
  try
    runLinters stx
  finally
    setInfoState { enabled := info.enabled }

-- A proof's declaration must exist before command linters inspect it. Drain
-- detached trees after declaration elaboration, still using their own source.
private def runProofLinters : CommandElabM Unit := do
  let pending := (cache.getState (← getEnv)).proofLints
  if pending.isEmpty then return
  modifyEnv fun env => cache.modifyState env fun s => { s with proofLints := #[] }
  for p in pending do
    let frontInfo ← getInfoState
    let original := (← get).messages
    modify fun s => { s with messages := p.messages.markAllReported }
    try
      withTheReader Command.Context (fun c => { c with fileName := p.path, fileMap := p.fileMap, ref := p.stx }) do
        withScope (fun _ => p.scope) do
          withProofScope p.activeScopes do
            lintProofTrees p.stx p.info
    finally
      modify fun s => { s with
        infoState := frontInfo
        messages := original ++ locatedMessages p.path { s.messages with reported := {} } }

-- Isolate the block's message log, so only this block's errors are downgraded.
-- Restoring its tactic state before sorry avoids keeping a partially failed term.
private def execute (b : Block) (unit : Name) : TacticM Unit := do
  let helperRoot := unit ++ `Proofs
  let original ← Core.getMessageLog
  Core.setMessageLog {}
  let state ← saveState
  let before ← getEnv
  let isStrict ← strict
  let front ← readThe Core.Context
  let frontInfo ← getInfoState
  setInfoState { enabled := frontInfo.enabled }
  let pending ← try
    withTheReader Core.Context (fun c => { c with
        fileName := b.path, fileMap := b.fileMap,
        currNamespace := b.scope.currNamespace,
        openDecls := .simple helperRoot [] :: b.scope.openDecls ++ front.openDecls }) do
      withRef b.stx do
        let lintStx ← withSaveInfoContext do
          let mut lintStx := b.stx
          Lean.pushScope
          try
            for ns in b.activeScopes do Lean.activateScoped ns
            Lean.activateScoped helperRoot
            let term ← parseBody b
            lintStx ← `(command| example : _ := $term)
            let goal ← getMainGoal
            withInfoContext (evalTactic (← `(tactic| exact $term))) do
              -- Preserve Lean's body boundary so unusedVariables honors its
              -- analyzeTactics option on these independently linted trees.
              return Term.mkBodyInfo term (← getExprMVarAssignment? goal)
            if !(← getUnsolvedGoals).isEmpty then throwError "attached: proof left unsolved goals"
          catch ex =>
            if ex.isInterrupt then throw ex
            if !isAbortException ex then logException ex
          finally
            Lean.popScope
          let changes ← isolationChanges before
          unless changes.isEmpty do
            logError (MessageData.tagged `Attach.forbiddenSyntax
              m!"{String.intercalate "; " changes}")
          addTraceAsMessages
          return lintStx
        retainLocations b.path
        let mut info ← getInfoState
        if let some name ← Term.getDeclName? then
          info := { info with trees := info.trees.map fun
            | .context (.commandCtx ctx) tree =>
              .context (.commandCtx ctx) (.context (.parentDeclCtx name) tree)
            | tree => tree }
        pure { b.toSaved with
          stx := lintStx
          info := info
          messages := ← Core.getMessageLog
          scope := { b.scope with opts := ← getOptions, openDecls := (← readThe Core.Context).openDecls }
          activeScopes := helperRoot :: b.activeScopes : ProofLint }
  finally
    setInfoState frontInfo
  let messages ← Core.getMessageLog
  let hard := messages.unreported.any (fun m => m.data.hasTag (fun tag => tag == `Attach.unsupportedSuffix || tag == `Attach.forbiddenSyntax))
  if messages.hasErrors then
    state.restore
    closeMainGoal `attached (← mkSorry (← getMainTarget) true)
  Core.setMessageLog (original ++ { messages with unreported := messages.unreported.map fun m =>
    if m.severity == .error && !isStrict && !hard then { m with severity := .warning } else m })
  -- In standalone checks these trees already belong to the ambient source.
  -- Keep them for Lean's command linters and language-server queries.
  if front.fileName == b.path then
    modifyInfoState fun s => { s with trees := s.trees ++ pending.info.trees }
  else
    modifyEnv fun env => cache.modifyState env fun s => { s with proofLints := s.proofLints.push pending }

elab "attach_block " id:ident " in " unit:ident : tactic => do
  let some b := (cache.getState (← getEnv)).blocks.find? id.getId
    | throwError "missing cached proof"
  execute b unit.getId

@[command_elab proofBlock] def elabProofBlock : CommandElab := fun stx => do
  let id := stx[1]
  let name := (← getCurrNamespace) ++ id.getId
  let s := cache.getState (← getEnv)
  let block : Block := { (← save stx[3]) with helperCount := s.helpers.size }
  if s.including && s.blocks.contains name then throwErrorAt id "duplicate proof_of {name}"
  modifyEnv fun env => cache.modifyState env fun s => { s with blocks := s.blocks.insert name block }
  unless s.including do
    let some r := (records.getState (← getEnv)).find? name
      | throwErrorAt id "unknown front theorem {name}; import its front first"
    let env ← getEnv
    let unit := env.getModuleIdxFor? name |>.map (fun i => env.header.moduleNames[i.toNat]!)
    let unit := unit.getD name.getPrefix
    let olean ← findOLean unit
    if (← olean.metadata).modified < (← (System.FilePath.mk (← getFileName)).metadata).modified then
      logWarning "standalone: front snapshot is stale; run lake build"
    let ci ← getConstInfo name
    withScope (fun s => { s with
        levelNames := ci.levelParams ++ s.levelNames
        opts := s.opts.setBool `Elab.async false }) do
      elabCommand (← `(example : attached_type% $(mkIdent r.name) := by
        attach_replay $(mkIdent r.name) => attach_block $(mkIdent name) in $(mkIdent unit)))

@[command_elab unsupportedTermination, command_elab unsupportedDecreasing]
def rejectTermination : CommandElab := fun stx =>
  throwErrorAt stx "termination_by on attached theorems is unsupported (including decreasing_by)"

private def validateCommand (cmd : Syntax) : CommandElabM Unit := do
  if cmd.isOfKind ``unsupportedTermination || cmd.isOfKind ``unsupportedDecreasing then
    rejectTermination cmd
  if hasAtom cmd "private" then throwErrorAt cmd "private is forbidden in proof files"
  if cmd.isOfKind ``proofBlock || cmd.isOfKind ``helperDecl then return
  if [``Parser.Command.namespace, ``Parser.Command.end, ``Parser.Command.section,
      ``Parser.Command.open].contains cmd.getKind then return
  throwErrorAt cmd "unsupported proof-file command {firstAtom cmd}; use helper theorem or helper def"

private def load (path : String) : CoreM Unit := do
  if !(← System.FilePath.pathExists path) then
    modifyEnv fun env => cache.modifyState env fun s => { s with loaded := path :: s.loaded }
    return
  let before ← getEnv
  let input := Parser.mkInputContext (← IO.FS.readFile path) path
  withTheReader Core.Context (fun c => { c with fileName := path, fileMap := input.fileMap }) do
    liftCommandElabM (throwOnError := false) do
      modifyEnv fun env => cache.modifyState env fun s => { s with including := true }
      Lean.pushScope
      try
        let (_, initial, messages) ← Parser.parseHeader input
        modify fun s => { s with messages := s.messages ++ messages }
        let mut ps := initial
        repeat
          let (cmd, next, messages) := Parser.parseCommand input
            { env := ← getEnv, options := ← getOptions } ps (← get).messages
          ps := next
          modify fun s => { s with messages }
          if Parser.isTerminalCommand cmd then break
          try
            validateCommand cmd
            -- The implicit loader scope cannot be closed by proof-file `end`.
            if cmd.isOfKind ``Parser.Command.end && (← getScopes).length == 1 then
              throwErrorAt cmd "unmatched end in proof file"
            elabCommand cmd
          catch ex => logException ex
        pure ()
      finally
        -- Also unwind unclosed namespace/section commands on malformed input.
        for _ in [: (← getScopes).length] do Lean.popScope
        -- Keep only recorded attachment data, including on a loader failure.
        let saved := cache.getState (← getEnv)
        setEnv (cache.setState before { saved with including := false, loaded := path :: saved.loaded })
    retainLocations path

private def runHelpers (count : Nat) (unit : Name) : CommandElabM Unit := do
  let helperRoot := unit ++ `Proofs
  let s := cache.getState (← getEnv)
  for i in [s.done:count] do
    let h := s.helpers[i]!
    let before ← getEnv
    withTheReader Command.Context (fun c => { c with fileName := h.path, fileMap := h.fileMap, ref := h.stx }) do
      let frontInfo ← getInfoState
      setInfoState { enabled := frontInfo.enabled }
      try
        withScope (fun _ => { h.scope with
            currNamespace := helperRoot
            openDecls := .simple h.scope.currNamespace [] :: h.scope.openDecls,
            opts := h.scope.opts.setBool `Elab.async false }) do
          withProofScope (helperRoot :: h.activeScopes) do
            withProofWindow (elabHelper h.stx)
            lintProofTrees h.stx (← getInfoState)
      finally
        setInfoState frontInfo
        let changes ← liftCoreM (isolationChanges before)
        unless changes.isEmpty do
          setEnv before
          modifyEnv fun env => cache.modifyState env fun s =>
            { s with failedHelper := s.failedHelper.or (some i) }
          liftCoreM do
            logErrorAt h.stx m!"helper {h.stx[1][1][0]}: {String.intercalate "; " changes}"
            retainLocations h.path
        modifyEnv fun env => cache.modifyState env fun s => { s with done := i + 1 }
        modify fun s => { s with messages := locatedMessages h.path s.messages }

-- Lean has fully elaborated the statement and binders before entering this
-- tactic. Loading commands here cannot influence that statement's meaning.
elab "attach_run " path:str : tactic => withMainContext do
  let some name ← Term.getDeclName? | throwError "attachment requires a theorem"
  if Shadow.isActive (← getEnv) then
    modifyEnv fun env => Shadow.recordAttached env name
    closeMainGoal `attached (← mkSorry (← getMainTarget) false)
    return
  Term.synthesizeSyntheticMVarsNoPostponing
  let unit := (← getEnv).mainModule
  let locals := (← getLCtx).foldl (fun ns d =>
    if d.isImplementationDetail then ns else ns ++ [d.userName]) []
  if !(cache.getState (← getEnv)).loaded.contains path.getString then load path.getString
  let s := cache.getState (← getEnv)
  if let some block := s.blocks.find? name then
    liftCommandElabM (runHelpers block.helperCount unit) (throwOnError := false)
  modifyEnv fun env => records.addEntry env ⟨name, path.getString, locals⟩
  modifyEnv fun env => cache.modifyState env fun s => { s with used := s.used.insert name }
  let some block := s.blocks.find? name
    | if ← strict then throwError "attached: no proof for {name} in {path.getString}"
      logWarning m!"attached: no proof for {name} in {path.getString}"
      closeMainGoal `attached (← mkSorry (← getMainTarget) false)
      return
  if let some failed := (cache.getState (← getEnv)).failedHelper then
    if failed < block.helperCount then
      logWarning m!"attached: skipping proof for {name} after helper isolation failure"
      closeMainGoal `attached (← mkSorry (← getMainTarget) false)
      return
  execute block unit

@[command_elab attachedDecl, command_elab bodilessDecl] def elabAttached : CommandElab := fun stx => do
  let shadowMode := Shadow.isActive (← getEnv)
  unless shadowMode || (cache.getState (← getEnv)).shadow.isSome do
    let (snapshot, errors) ← Shadow.run (← read).fileMap.source (← getFileName)
      (← getEnv).mainModule (← getOptions) (← getEnv)
    for error in errors do logError error
    modifyEnv fun env => cache.modifyState env fun s => { s with shadow := some snapshot }
  let mods : TSyntax ``Parser.Command.declModifiers := ⟨stx[0]⟩
  if hasAtom mods "private" then throwError "attached theorems cannot be private"
  let shift := if stx.isOfKind ``attachedDecl then 1 else 0
  let id : TSyntax ``Parser.Command.declId := ⟨stx[2 + shift]⟩
  let sig : TSyntax ``Parser.Command.declSig := ⟨stx[3 + shift]⟩
  let unit := (← getEnv).mainModule
  unless (← getEnv).contains (`AttachStamp ++ unit) do
    throwError "front must import {unit}.ProofsStamp"
  let overridePath := attach.proofFile.get (← getOptions)
  let cwd := (← IO.currentDir).toString ++ "/"
  let front : System.FilePath := ((← getFileName).dropPrefix cwd).toString
  let path := if overridePath.isEmpty then (front.withExtension "" / "Proofs.lean").toString else overridePath
  let action := do
    withScope (fun s => { s with opts := s.opts.setBool `Elab.async false }) do
      elabCommand (← `($mods:declModifiers theorem $id:declId $sig:declSig := by attach_run $(Syntax.mkStrLit path)))
  if shadowMode then action else withProofWindow action
  runProofLinters
  -- addDecl emits this declaration-level warning after execute has returned to
  -- the front context. Attribute it to the attached body, retaining its payload.
  unless shadowMode do
    let file ← getFileName
    let pos := (← read).fileMap.toPosition (id.raw.getPos?.getD 0)
    if (← get).messages.unreported.any (fun m =>
        m.fileName == file && m.pos == pos && m.data.hasTag (· == `hasSorry)) then
      let ident := if id.raw.isIdent then id.raw else id.raw[0]
      let name ← liftCoreM (resolveGlobalConstNoOverload ident)
      if let some b := (cache.getState (← getEnv)).blocks.find? name then
        modify fun s => { s with messages := locatedMessages b.path { s.messages with
          unreported := s.messages.unreported.map fun m =>
            if m.fileName == file && m.pos == pos && m.data.hasTag (· == `hasSorry) then
              { m with
                fileName := b.path
                pos := b.fileMap.toPosition (b.stx.getPos?.getD 0)
                endPos := b.stx.getTailPos?.map b.fileMap.toPosition }
            else m } }

@[command_elab Lean.Parser.Command.eoi] def checkUnused : CommandElab := fun _ => do
  if Shadow.isActive (← getEnv) || (← getEnv).mainModule == `Attach then return
  let file ← getFileName
  let s := cache.getState (← getEnv)
  if file.endsWith "Proofs.lean" && s.loaded.isEmpty then
    -- Standalone Lean elaborates commands normally; audit its command grammar
    -- as well, including files containing only disallowed declarations.
    modifyEnv fun env => cache.modifyState env fun s => { s with blocks := {}, helpers := #[] }
    liftCoreM (load file)
    return
  runHelpers s.helpers.size (← getEnv).mainModule
  let s := cache.getState (← getEnv)
  if let some snapshot := s.shadow then
    Shadow.check snapshot (← getEnv) s.proofConstants
      ((← getEnv).mainModule ++ `Proofs) (← liftCoreM strict)
  for (name, block) in s.blocks.toList do
    if !s.used.contains name && !s.loaded.isEmpty then
      withTheReader Command.Context (fun c => { c with fileName := block.path, fileMap := block.fileMap }) do
        logWarningAt block.stx m!"unknown front theorem {name} in {block.path}"
        liftCoreM (retainLocations block.path)
end Attach
