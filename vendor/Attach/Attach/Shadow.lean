import Lean

open Lean Elab Command

register_option attach.shadow : Bool := {
  defValue := false, descr := "Internal attachment-free shadow elaboration"
}

namespace Attach.Shadow

/-- The writer records original direct proof debt on the statement, before any
proof file is loaded. Proof-file attributes cannot grant this permission. -/
initialize debtAttr : TagAttribute ←
  registerTagAttribute `attach_debt "Original theorem proof contains recorded sorry debt"

-- The environment flag is authoritative, not a proof-controlled option.
private initialize mode : EnvExtension Bool ← registerEnvExtension (pure false)
private initialize attachedNames : EnvExtension NameSet ← registerEnvExtension (pure {})

def isActive (env : Environment) : Bool := mode.getState env

def recordAttached (env : Environment) (name : Name) : Environment :=
  attachedNames.modifyState env (·.insert name)

structure Snapshot where
  imported : Environment
  env : Environment
  declarations : NameMap ConstantInfo
  attachedNames : NameSet

/-- Run before any proof file is read. Only the front's imports seed this environment.
Errors retain their source line, including the declaration being elaborated. -/
def run (source file : String) (unit : Name) (opts : Options)
    (frontEnv : Environment) : IO (Snapshot × Array String) := do
  let input := Parser.mkInputContext source file
  let (_, parser, messages) ← Parser.parseHeader input
  let some imported := frontEnv.importEnv?
    | throw (IO.userError "shadow pass: missing import-only environment")
  let imported := imported.setMainModule unit
  let opts := opts.setBool `attach.shadow true
  let env := mode.setState imported true
  let result ← IO.processCommands input parser (Command.mkState env messages opts)
  let mut errors := #[]
  for msg in result.commandState.messages.toList do
    if msg.severity == .error then
      let line := source.splitOn "\n" |>.toArray |>.getD (msg.pos.line - 1) ""
      errors := errors.push s!"shadow pass failed in {line}: {← msg.data.toString}"
  let env := result.commandState.env
  let declarations : NameMap ConstantInfo := env.constants.foldStage2 (s := {}) fun ds n ci =>
    if imported.constants.contains n then ds else ds.insert n ci
  return (⟨imported, env, declarations, attachedNames.getState env⟩, errors)

/-- Only imported proof-window realizations need a fresh mutable realization
cache. Allocate it once on demand; ordinary shadow elaboration reuses imports. -/
private def isolateImports (snapshot : Snapshot) (opts : Options) : IO Environment := do
  let original := snapshot.imported
  let level := if original.header.isModule then
    if Elab.inServer.get opts then OLeanLevel.server else .exported
    else .private
  let mut imported ← importModules original.header.imports opts original.header.trustLevel
    (loadExts := false) (level := level)
  for ext in (← persistentEnvExtensionsRef.get) do
    let state := ext.toEnvExtension.getState original (asyncMode := .sync)
    imported := ext.toEnvExtension.setState imported state (asyncMode := .sync)
  return imported.setMainModule original.mainModule

private def equalExpr (a b : ConstantInfo) (x y : Expr) : Bool :=
  x.eqv (y.instantiateLevelParams b.levelParams (a.levelParams.map Level.param))

/-- Longest proper owner prefix in the full constant table, including private
owners. The branch-local Environment lookup can hide realized splitter helpers. -/
private def auxiliaryOwner? (env : Environment) (name : Name) : Option Name :=
  find name.getPrefix
where
  find : Name → Option Name
    | .anonymous => none
    | parent@(.str pfx _) | parent@(.num pfx _) =>
      if env.constants.contains parent then some parent
      else if env.constants.contains (privateToUserName parent) then
        some (privateToUserName parent)
      else if env.constants.contains (mkPrivateName env parent) then
        some (mkPrivateName env parent)
      else find pfx

/-- Known Lean generator kinds accept decimal index chains of any depth.
An arbitrary numbered name needs native metadata; stable compiler products
retain their ordinary per-declaration comparison. -/
private def numberedAuxiliary (suffix : String) : Bool :=
  let digits := fun (s : String) => !s.isEmpty && s.toList.all Char.isDigit
  let parts := (suffix.splitOn "_").reverse
  let indices := parts.takeWhile digits
  let kind := String.intercalate "_" (parts.drop indices.length).reverse
  !indices.isEmpty &&
    ["match", "_match", "proof", "eq", "_eq", "_proof", "_simp", "_sparseCasesOn", "_auxLemma"].contains kind

/-- Structural recursion registers its abbrev functionals in this native table;
there is no structural equation record for theorem owners. A bare _f is not enough. -/
private def recursionFunctional (env : Environment) (name : Name) : Bool :=
  name == name.getPrefix ++ `_f &&
    (env.constants.find? name).any (fun info => match info with
      | .defnInfo info => info.hints == .abbrev
      | _ => false) &&
    (defHeightOverrideExt.getState env (asyncMode := .async .asyncEnv) (asyncDecl := name)).contains name

/-- Native metadata establishes auxiliary identity and proof-window provenance.
The public sparse casesOn registry (written alongside its private generator cache)
and structural functional table cover definitions
which are neither matchers nor cached auxiliary lemmas. -/
private def nativeAuxiliary (env : Environment) (name : Name) : Bool :=
  Meta.isMatcherCore env name ||
    (Meta.getSparseCasesOnInfoCore env name).isSome ||
    recursionFunctional env name ||
    (Meta.auxLemmasExt.getState env (asyncMode := .async .asyncEnv) (asyncDecl := name)).lemmas.toList.any
      (fun (_, lemma) => lemma.1 == name)

/-- Stop at the longest known owner; every intervening component must be
a known indexed kind, natively registered, or reserved. Stable compiler products
retain their own comparison, including structural functionals with native metadata. -/
private def declarationAuxiliary (env : Environment) (name : Name) : Bool :=
  env.constants.contains name &&
    (declRangeExt.find? (level := .exported) env name).isNone &&
    (declRangeExt.find? (level := .server) env name).isNone && generatedPath name
where
  generatedPath : Name → Bool
    | n@(.str parent suffix) =>
      !["_default", "_unsafe_rec", "_f", "_unary", "_mutual"].contains suffix &&
        (numberedAuxiliary suffix || suffix == "splitter" ||
          isReservedName env n || isReservedName env (privateToUserName n) ||
          nativeAuxiliary env n) &&
        (env.constants.contains parent || env.constants.contains (privateToUserName parent) ||
          env.constants.contains (mkPrivateName env parent) || generatedPath parent)
    | _ => false

/-- Normalize generated definitions independently in their own full environment.
The theorem marker records only the statement: this comparison-only expression
never enters the environment or kernel, and never contains the theorem's proof. -/
private partial def canonicalizeAuxiliaries (env : Environment) (e : Expr)
    (expanding : NameSet := {}) : Expr :=
  -- Avoid rebuilding expressions that contain no generated references.
  if (e.find? fun e => match e with
      | .const name _ => declarationAuxiliary env name
      | _ => false).isNone then e
  else e.replace fun e => do
    let .const name levels := e | none
    guard (!expanding.contains name && declarationAuxiliary env name)
    let info ← env.constants.find? name
    let expanding := expanding.insert name
    match info with
    | .thmInfo info =>
      return mkApp (mkConst `Attach.Shadow.auxiliaryProof)
        (canonicalizeAuxiliaries env
          (info.type.instantiateLevelParams info.levelParams levels) expanding)
    | .defnInfo info =>
      return canonicalizeAuxiliaries env
        (info.value.instantiateLevelParams info.levelParams levels) expanding
    | _ => none

private def equalCanonical (snapshot : Snapshot) (env : Environment)
    (a b : ConstantInfo) (x y : Expr) : Bool :=
  equalExpr a b (canonicalizeAuxiliaries snapshot.env x) (canonicalizeAuxiliaries env y)

/-- Include recursor computation rules: inductives and structures have no value?. -/
private def equalDefinition (snapshot : Snapshot) (env : Environment)
    (a b : ConstantInfo) : Bool := Id.run do
  match a, b with
  | .thmInfo _, .thmInfo _ => return true
  | .thmInfo _, _ | _, .thmInfo _ => return false
  | _, _ => pure ()
  match a.value? (allowOpaque := true), b.value? (allowOpaque := true) with
  | some x, some y =>
    return equalCanonical snapshot env a b x y
  | none, none =>
    match a, b with
    | .inductInfo x, .inductInfo y =>
      return { x with type := y.type, levelParams := y.levelParams } == y
    | .ctorInfo x, .ctorInfo y =>
      return { x with type := y.type, levelParams := y.levelParams } == y
    | .recInfo x, .recInfo y =>
      return { x with type := y.type, levelParams := y.levelParams, rules := y.rules } == y &&
        x.rules.length == y.rules.length && (x.rules.zip y.rules).all fun (r, s) =>
          r.ctor == s.ctor && r.nfields == s.nfields && equalCanonical snapshot env a b r.rhs s.rhs
    | .axiomInfo _, .axiomInfo _ => return true
    | .quotInfo _, .quotInfo _ => return true
    | _, _ => return false
  | _, _ => return false

/-- Proof-local names need provenance as well as ownership. Direct addDecl calls
cannot borrow a numbered name: generated lemmas/matchers have Lean metadata;
named local definitions have ranges and well-founded-definition metadata. -/
def proofAuxiliary (env : Environment) (attachedNames : NameSet)
    (name : Name) : Bool :=
  (attachedNames.toList.any fun owner =>
    owner != privateToUserName name && owner.isPrefixOf (privateToUserName name)) &&
    (nativeAuxiliary env name ||
      -- Well-founded theorem compilation has no WF equation-info record.
      -- Its packed unary theorem does carry Lean's native recursion tag.
      (name == name.getPrefix ++ `_unary &&
        attachedNames.contains (privateToUserName name.getPrefix) &&
        Meta.recExt.isTagged env name &&
        (env.constants.find? name).any (·.isTheorem)) ||
      Meta.Match.isMatchEqnTheorem env name ||
      (Meta.Match.matchEqnsExt.getState env (asyncMode := .async .asyncEnv) (asyncDecl := name)).map.toList.any
        (fun (_, eqns) => eqns.splitterName == name) ||
      (name == name.getPrefix ++ `_arg_pusher &&
        [name.getPrefix, privateToUserName name.getPrefix].any (fun matcher =>
          Meta.isMatcherCore env matcher && (Elab.WF.eqnInfoExt.find? env matcher.getPrefix).isSome)) ||
      (declRangeExt.find? (level := .exported) env name).isSome ||
      ((Elab.WF.eqnInfoExt.find? env name.getPrefix).isSome &&
        (name == Compiler.mkUnsafeRecName name.getPrefix ||
          name == Meta.mkEqLikeNameFor env name.getPrefix Meta.unfoldThmSuffix)))

/-- Lean 4.35's matcher predicate strips the private prefix before lookup, so
equations and splitters of private matchers need the original, verified prefix.
Splitter realization can also create internal descendants of known matchers. -/
private def reservedRealization (snapshot : Snapshot) (env : Environment) (name : Name) : Bool :=
  isReservedName env name || isReservedName env (privateToUserName name) || (Id.run do
    let .str parent suffix := name | return false
    unless Meta.isEqnReservedNameSuffix suffix || suffix == "splitter" do return false
    return [parent, privateToUserName parent].any fun p =>
      knownMatcher p) || matcherAuxiliary (privateToUserName name)
where
  knownMatcher (name : Name) : Bool :=
    snapshot.env.constants.contains name && Meta.isMatcherCore snapshot.env name
  -- Walk up to the longest proper matcher prefix, validating every suffix component.
  matcherAuxiliary : Name → Bool
    | .str parent suffix =>
      (suffix == "splitter" || Meta.isEqnReservedNameSuffix suffix || suffix.startsWith "_") &&
        (knownMatcher parent || matcherAuxiliary parent)
    | _ => false

-- Run Lean's generators on the shadow side, never on proof-controlled state.
-- Keep the resulting environment for subsequent names from the same realization.
private def realizeExpected (env : Environment) (name : Name) : CoreM (Option Environment) := do
  let saved : Core.State ← get
  set ({ env := env } : Core.State)
  try
    executeReservedNameAction name
    if !(← getEnv).constants.contains name then
      -- Lean's registered matcher handler misses private matcher prefixes.
      if let .str parent suffix := name then
        if Meta.isEqnReservedNameSuffix suffix || suffix == "splitter" then
          for owner in [parent, privateToUserName parent] do
            if Meta.isMatcherCore (← getEnv) owner then
              discard <| Meta.MetaM.run' <| Meta.Match.getEquationsForImpl owner
    let result ← getEnv
    return if result.constants.contains name then some result else none
  catch ex =>
    if ex.isInterrupt then throw ex
    return none
  finally
    set saved

private def equalConstant (snapshot : Snapshot) (env : Environment)
    (expected actual : ConstantInfo) : Bool :=
  expected.levelParams.length == actual.levelParams.length &&
    equalCanonical snapshot env expected actual expected.type actual.type &&
    equalDefinition snapshot env expected actual

-- Numbered children of a matcher/realization are generated as part of the
-- parent's realization. A plain front/imported owner is not sufficient.
private def checkedRealization (snapshot : Snapshot) (env : Environment)
    (name : Name) : CoreM (Option Environment) := do
  let mut expected := snapshot.env
  if reservedRealization snapshot env name then
    if let some result ← realizeExpected expected name then expected := result
  if !expected.constants.contains name && declarationAuxiliary env name then
    if let some owner := auxiliaryOwner? env name then
      if Meta.isMatcherCore expected owner then
        if let some result ← realizeExpected expected (owner ++ `splitter) then expected := result
      else if reservedRealization snapshot env owner then
        if let some result ← realizeExpected expected owner then expected := result
  let some a := expected.constants.find? name | return none
  let some b := env.constants.find? name | return none
  return if equalConstant { snapshot with env := expected } env a b then some expected else none

/-- Trace sorry dependencies only when the axiom audit finds sorryAx. Recorded
direct body debt and preserved inherited debt are accepted. New statement or
helper debt remains an error, and unrecorded attached debt remains WIP. -/
private structure SorrySources where
  visited : NameSet := {}
  attached : NameSet := {}
  unexpected : Bool := false
  preserved : NameSet := {}
  -- These owners may have direct body debt; their types must still be visited.
  recorded : NameSet := {}
  inherited : Bool := false

private partial def collectSorrySources (env : Environment) (attached : NameSet)
    (name : Name) : StateT SorrySources CoreM Unit := do
  if (← get).visited.contains name then return
  modify fun s => { s with visited := s.visited.insert name }
  unless (← collectAxioms name).contains ``sorryAx do return
  -- Original imported debt and exactly preserved front debt are inherited;
  -- local proof helpers and new attached sorries still undergo the audit.
  if (← get).preserved.contains name then
    modify fun s => { s with inherited := true }
    return
  let some info := env.constants.find? name
    | modify fun s => { s with unexpected := true }; return
  let owner := if attached.contains name then some name else
    if nativeAuxiliary env name then
      attached.toList.find? (fun n => n.isPrefixOf (privateToUserName name))
    else none
  let visitExpr (e : Expr) (source : Option Name) := do
    for dep in e.getUsedConstants do
      if dep == ``sorryAx then
        match source with
        | some n => modify fun s =>
          if s.recorded.contains n then { s with inherited := true }
          else { s with attached := s.attached.insert n }
        | none => modify fun s => { s with unexpected := true }
      else collectSorrySources env attached dep
  visitExpr info.type none
  if let some value := info.value? (allowOpaque := true) then visitExpr value owner
  if let .inductInfo info := info then
    for ctor in info.ctors do collectSorrySources env attached ctor

/-- Lean.Meta.nativeEqTrue uses mkAuxDeclName (`_native ++ tacticName ++ `ax).
Both native_decide and decide +native call it; require decimal generator indices. -/
private def nativeDecideOwner? (name : Name) : Option Name :=
  match name with
  | .str (.str (.str owner "_native") tactic) suffix =>
    if tactic != "native_decide" && tactic != "decide" then none else
    match suffix.splitOn "_" with
    | "ax" :: indices =>
      if !indices.isEmpty && indices.all (fun s => !s.isEmpty && s.toList.all Char.isDigit)
      then some owner else none
    | _ => none
  | _ => none

private def nativeDecideAxiom (name : Name) : Bool :=
  (nativeDecideOwner? name).isSome

/-- An attached proof may reuse native evidence from a compared kept declaration.
The original body supplies permission; names introduced by proofs or their
helpers cannot grant it. Keep the exact owner, including its private prefix. -/
private def keptNativeAxiom (snapshot : Snapshot) (actual : Environment)
    (axiomName : Name) : CoreM Bool := do
  let some owner := nativeDecideOwner? axiomName | return false
  if snapshot.attachedNames.contains owner || declarationAuxiliary snapshot.env owner then return false
  let some expected := snapshot.declarations.find? owner | return false
  let some realized := actual.constants.find? owner | return false
  unless (expected.value? (allowOpaque := true)).isSome &&
      equalConstant snapshot actual expected realized do return false
  let originalAxioms ← withEnv snapshot.env (collectAxioms owner)
  return originalAxioms.any (fun ax => ax == `Lean.ofReduceBool || nativeDecideAxiom ax)

/-- Attached proofs may use axioms from the front's original import closure or
reviewed kept native owners. Kept theorems and realizations retain the original-
dependency rule. WIP sorry sources are returned for grouped diagnostics. -/
private def checkTheoremAxioms (snapshot : Snapshot) (original actual : Environment)
    (name origin : Name) : CommandElabM NameSet := do
  let used ← liftCoreM <| withEnv actual (collectAxioms name)
  let nonstandard := used.filter fun ax =>
    ![``propext, ``Classical.choice, ``Quot.sound].contains ax
  let mut incomplete : NameSet := {}
  unless nonstandard.isEmpty do
    let allowed ← liftCoreM <| withEnv original (collectAxioms origin)
    for ax in nonstandard do
      if ax == ``sorryAx then
        let mut preserved : NameSet := snapshot.imported.constants.fold (init := {}) fun names n _ => names.insert n
        let mut recorded : NameSet := {}
        for (kept, expected) in snapshot.declarations.toList do
          if snapshot.attachedNames.contains kept then
            if debtAttr.hasTag snapshot.env kept then recorded := recorded.insert kept
            continue
          let some oldBody := expected.value? (allowOpaque := true) | continue
          unless oldBody.getUsedConstants.contains ``sorryAx do continue
          let some realized := actual.constants.find? kept | continue
          let some newBody := realized.value? (allowOpaque := true) | continue
          -- Admit only the same pre-existing direct debt, with exact type and
          -- body comparison. A proof-file helper cannot grant this permission.
          if equalExpr expected realized expected.type realized.type &&
              equalExpr expected realized oldBody newBody then
            preserved := preserved.insert kept
        let (_, sources) ← liftCoreM <| withEnv actual <|
          (collectSorrySources actual snapshot.attachedNames name).run { preserved, recorded }
        incomplete := sources.attached
        if sources.unexpected || (incomplete.isEmpty && !sources.inherited) ||
            (sources.inherited && !snapshot.attachedNames.contains name && !allowed.contains ax) then
          logError m!"shadow pass: {name}: proof file changed its elaboration (unexpected axiom {ax})"
      else if snapshot.attachedNames.contains name then
        unless snapshot.imported.constants.contains ax ||
            (← liftCoreM <| keptNativeAxiom snapshot actual ax) do
          logError m!"shadow pass: {name}: proof file changed its elaboration (unexpected axiom {ax})"
      else if ax == `Lean.ofReduceBool || nativeDecideAxiom ax then
        unless allowed.any (fun ax => ax == `Lean.ofReduceBool || nativeDecideAxiom ax) do
          logError m!"shadow pass: {name}: proof file changed its elaboration (unexpected axiom {ax})"
      else unless snapshot.imported.constants.contains ax && allowed.contains ax do
        logError m!"shadow pass: {name}: proof file changed its elaboration (unexpected axiom {ax})"
  return incomplete

/-- Follow generated owners to the imported matcher behind a private splitter.
A local declaration stops the search, even under an imported namespace (Nat.f). -/
private partial def hasImportedOwner (env : Environment) (name : Name) : Bool :=
  (auxiliaryOwner? env name).any fun owner =>
    (env.getModuleIdxFor? owner).isSome ||
      (declarationAuxiliary env owner && hasImportedOwner env owner)

def check (snapshot : Snapshot) (env : Environment) (created : NameSet)
    (helperRoot : Name) (isStrict : Bool := false) : CommandElabM Unit := do
  let mut incomplete : NameMap NameSet := {}
  let recordIncomplete (pending : NameMap NameSet) (name : Name) (sources : NameSet) :=
    sources.toList.foldl (fun pending source =>
      pending.insert source (((pending.find? source).getD {}).insert name)) pending
  for (name, expected) in snapshot.declarations.toList do
    if declarationAuxiliary snapshot.env name then continue
    let some actual := env.constants.find? name
      | logError m!"shadow pass: {name}: proof file changed its elaboration (declaration missing)"; continue
    unless equalConstant snapshot env expected actual do
      logError m!"shadow pass: {name}: proof file changed its elaboration (type or definition differs)"
    if expected.isTheorem && actual.isTheorem then
      let sources ← checkTheoremAxioms snapshot snapshot.env env name name
      incomplete := recordIncomplete incomplete name sources
  let mut reference := snapshot
  let mut isolated : Option Snapshot := none
  for (name, actual) in env.constants.foldStage2 (s := #[]) (fun xs n ci => xs.push (n, ci)) do
    if helperRoot.isPrefixOf (privateToUserName name) ||
        snapshot.attachedNames.contains name || proofAuxiliary env snapshot.attachedNames name then continue
    if created.contains name then
      -- Do not bypass validation just because the shadow already realized it.
      -- Imported caches are shared by the fast shadow run, so these always use
      -- the independent verifier, even if the name now appears in snapshot.env.
      let imported := hasImportedOwner snapshot.env name
      if imported && isolated.isNone then
        let clean ← isolateImports snapshot (← getOptions)
        isolated := some { snapshot with env := clean }
      let verifier := if imported then isolated.getD reference else reference
      -- Select the compiled owner before realization; a regenerated lemma's
      -- proof cannot grant permission to use nonstandard imported axioms.
      let origin := (auxiliaryOwner? verifier.env name).getD name
      if let some expected ← liftCoreM (checkedRealization verifier env name) then
        if actual.isTheorem then
          let sources ← checkTheoremAxioms snapshot verifier.env env name origin
          incomplete := recordIncomplete incomplete name sources
        if imported then isolated := some { verifier with env := expected }
        else reference := { reference with env := expected }
        continue
    else if snapshot.env.constants.contains name || reservedRealization snapshot env name ||
        (declarationAuxiliary env name &&
          (auxiliaryOwner? env name).any snapshot.env.constants.contains) then continue
    logError m!"shadow pass: {name}: proof file changed its elaboration (unexpected declaration)"

  for (source, names) in incomplete.toList do
    let dependents := ((names.toArray.qsort Name.lt).toList.filter (· != source)).map toString
    let suffix := if dependents.isEmpty then "" else
      s!"; dependents {String.intercalate ", " dependents} inherit sorryAx"
    let message := m!"shadow pass: attached proof of {source} is incomplete (sorry){suffix}"
    if isStrict then logError message else logWarning message

end Attach.Shadow
