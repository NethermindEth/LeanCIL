import Lean
import Lean.Replay

/-! Shared kernel replay of an exact target set, used by certification and the native auditor. -/

namespace CIL.Replay

/-- Reads exported imports and complete declarations from every available module part. -/
unsafe def readReplayParts (module : Lean.Name) : IO (Lean.ModuleData × Lean.ModuleData) := do
  let modulePath ← Lean.findOLean module
  unless (← modulePath.pathExists) do
    throw <| IO.userError s!"object file '{modulePath}' of module {module} does not exist"
  let mut paths := #[modulePath]
  let serverPath := Lean.OLeanLevel.server.adjustFileName modulePath
  if (← serverPath.pathExists) then
    paths := paths.push serverPath
    let privatePath := Lean.OLeanLevel.private.adjustFileName modulePath
    if (← privatePath.pathExists) then paths := paths.push privatePath
  let parts ← Lean.readModuleDataParts paths
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  return (parts[0].1, parts[parts.size - 1].1)

/-- Identical on-demand theorem declarations obey the toolchain replay duplicate rule. -/
def sameReplayTheorem : Lean.ConstantInfo → Lean.ConstantInfo → Bool
  | .thmInfo first, .thmInfo second => first.name == second.name && first.type == second.type &&
      first.levelParams == second.levelParams && first.all == second.all
  | _, _ => false

/-! Kernel replay with concurrent declaration checks, adapted from `Lean.Kernel.Environment.replay`.
Each definition, theorem, opaque and axiom is added unchecked in dependency order and then
checked against the environment that preceded it, which is exactly what sequential replay checks.
Inductives, the quotient and postponed constructor/recursor comparisons stay sequential. -/

/-- Checking-boundary failures that can identify a rejected owned declaration. -/
inductive RejectionKind where
  | unknownConstant | alreadyDeclared | declTypeMismatch | declHasMVars | declHasFVars
  | funExpected | typeExpected | letTypeMismatch | exprTypeMismatch | appTypeMismatch
  | invalidProj | thmTypeIsNotProp | constructorMismatch | recursorMismatch
  deriving BEq, Repr

/-- Classifies kernel failures without interpreting diagnostic text. -/
def rejectionKind : Lean.Kernel.Exception → Option RejectionKind
  | .unknownConstant .. => some .unknownConstant
  | .alreadyDeclared .. => some .alreadyDeclared
  | .declTypeMismatch .. => some .declTypeMismatch
  | .declHasMVars .. => some .declHasMVars
  | .declHasFVars .. => some .declHasFVars
  | .funExpected .. => some .funExpected
  | .typeExpected .. => some .typeExpected
  | .letTypeMismatch .. => some .letTypeMismatch
  | .exprTypeMismatch .. => some .exprTypeMismatch
  | .appTypeMismatch .. => some .appTypeMismatch
  | .invalidProj .. => some .invalidProj
  | .thmTypeIsNotProp .. => some .thmTypeIsNotProp
  | .other .. | .deterministicTimeout | .excessiveMemory | .deepRecursion | .interrupted => none

/-- A declaration rejected at a kernel checking boundary. -/
structure ReplayRejection where
  declaration : Lean.Name
  kind : RejectionKind

/-- Diagnostic replay never establishes verification success. -/
inductive ReplayDiagnostic where
  | accepted
  | rejected (rejection : ReplayRejection)
  | unavailable (message : String)

/-- Kernel verdict for one deferred declaration check. -/
inductive CheckOutcome where
  | accepted
  | cancelled
  | rejected (message : String) (kind : Option RejectionKind)

/-- Constants being replayed and the deferred checks issued so far. -/
structure ReplayContext where
  newConstants : Std.HashMap Lean.Name Lean.ConstantInfo
  cancel : IO.CancelToken
  checks : IO.Ref (Array (Lean.Name × Task (Except IO.Error CheckOutcome)))
  rejection : IO.Ref (Option ReplayRejection)

/-- The environment built so far and the names still to replay. -/
structure ReplayState where
  env : Lean.Kernel.Environment
  remaining : Lean.NameSet := {}
  pending : Lean.NameSet := {}
  postponedConstructors : Lean.NameSet := {}
  postponedRecursors : Lean.NameSet := {}

abbrev ReplayM := ReaderT ReplayContext <| StateRefT ReplayState IO

/-- Renders a kernel exception as the toolchain replay does. -/
def kernelMessage (ex : Lean.Kernel.Exception) : IO String :=
  ex.toMessageData {} |>.toString

/-- Moves a name still to be replayed from `remaining` to `pending`. -/
def isTodo (name : Lean.Name) : ReplayM Bool := do
  if (← get).remaining.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  return false

/-- Kernel-checks one declaration against the environment that preceded it.
Written inline in `IO.asTask`, the check would run eagerly on the calling thread. -/
@[noinline] def checkDeclaration (before : Lean.Kernel.Environment) (decl : Lean.Declaration)
    (cancel : IO.CancelToken) : IO CheckOutcome := do
  match before.addDeclCore 0 0 decl (some cancel) with
  | .ok _ => return .accepted
  | .error .interrupted => return .cancelled
  | .error ex =>
    cancel.set
    return .rejected (← kernelMessage ex) (rejectionKind ex)

/-- Adds a declaration; a deferred check sees only the declarations added before it. -/
def addDecl (decl : Lean.Declaration) : ReplayM Unit := do
  let before := (← get).env
  match decl with
  | .defnDecl _ | .thmDecl _ | .opaqueDecl _ | .axiomDecl _ =>
    match before.addDeclWithoutChecking decl with
    | .error ex => throw <| .userError (← kernelMessage ex)
    | .ok env =>
      let cancel := (← read).cancel
      let check ← IO.asTask (checkDeclaration before decl cancel)
      let name := decl.getNames.headD .anonymous
      (← read).checks.modify (·.push (name, check))
      modify fun s => { s with env }
  | _ =>
    match before.addDeclCore 0 0 decl (cancelTk? := none) with
    | .ok env => modify fun s => { s with env }
    | .error ex =>
      let message ← kernelMessage ex
      if let some kind := rejectionKind ex then
        (← read).rejection.set (some ⟨decl.getNames.headD .anonymous, kind⟩)
      throw <| .userError message

/-- The constant `name` among those being replayed; a name the replay reaches but the replayed
    constants lack is an error naming it. -/
def replayedConstant (name : Lean.Name) : ReplayM Lean.ConstantInfo := do
  let some ci := (← read).newConstants[name]?
    | throw <| .userError s!"Constant {name} is not among the replayed constants"
  return ci

mutual
/-- Replays the constants a pending name uses, then the name itself. -/
partial def replayConstant (name : Lean.Name) : ReplayM Unit := do
  if ← isTodo name then
    let ci ← replayedConstant name
    replayConstants ci.getUsedConstantsAsSet
    -- A mutual block may already have replayed this name.
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo info => addDecl (.defnDecl info)
        | .thmInfo info =>
          -- Duplicate theorems are skipped as in the toolchain replay.
          if let some (.thmInfo prior) := (← get).env.find? ci.name then
            if info.name == prior.name && info.type == prior.type &&
                info.levelParams == prior.levelParams && info.all == prior.all then
              return
          addDecl (.thmDecl info)
        | .axiomInfo info => addDecl (.axiomDecl info)
        | .opaqueInfo info => addDecl (.opaqueDecl info)
        | .inductInfo info =>
          let all ← info.all.mapM replayedConstant
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            let .inductInfo member := ci
              | throw <| .userError s!"Constant {ci.name} in the mutual block of {name} is not \
                  an inductive"
            pure (ci, ← member.ctors.mapM replayedConstant)
          for (_, ctors) in ctorInfo do
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List Lean.InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name, type := ci.type,
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          addDecl (.inductDecl info.levelParams info.numParams types false)
        -- Constructors and recursors must equal those the replayed inductives generate.
        | .ctorInfo info =>
          modify fun s =>
            { s with postponedConstructors := s.postponedConstructors.insert info.name }
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          replayConstant `Eq
          addDecl .quotDecl
        modify fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

/-- Replays a set of constants in dependency order. -/
partial def replayConstants (names : Lean.NameSet) : ReplayM Unit := do
  for n in names do replayConstant n
end

/-- Requires replayed constructors and recursors to equal those generated by their inductives. -/
def checkPostponed : ReplayM Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if !(info == info') then
        (← read).rejection.set (some ⟨ctor, .constructorMismatch⟩)
        throw <| .userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| .userError s!"No such constructor {ctor}"
  for recursor in (← get).postponedRecursors do
    match (← get).env.find? recursor, (← read).newConstants[recursor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if !(info == info') then
        (← read).rejection.set (some ⟨recursor, .recursorMismatch⟩)
        throw <| .userError s!"Invalid recursor {recursor}"
    | _, _ => throw <| .userError s!"No such recursor {recursor}"

/-- Joins every deferred check and retains only the first terminal failure's classification. -/
def awaitChecks (checks : IO.Ref (Array (Lean.Name × Task (Except IO.Error CheckOutcome))))
    (rejection : IO.Ref (Option ReplayRejection)) : IO (Option String) := do
  let mut failure := none
  for (name, check) in ← checks.get do
    match ← IO.wait check with
    | .ok (.rejected message kind) =>
      if failure.isNone then rejection.set (kind.map fun kind => ⟨name, kind⟩)
      failure := failure <|> some s!"while replaying declaration '{name}':\n{message}"
    | .ok _ => pure ()
    | .error ex =>
      if failure.isNone then rejection.set none
      failure := failure <|> some s!"while replaying declaration '{name}':\n{ex}"
  return failure

/-- Kernel-checks every safe, total constant into `env`, accepting exactly what sequential replay
accepts.
Every deferred check has finished when this returns or throws, so imported regions may be freed. -/
def replay (newConstants : Std.HashMap Lean.Name Lean.ConstantInfo)
    (env : Lean.Kernel.Environment)
    (diagnostic : Option (IO.Ref (Option ReplayRejection)) := none) :
    IO Lean.Kernel.Environment := do
  let remaining := newConstants.fold (init := {}) fun remaining name ci =>
    if !ci.isUnsafe && !ci.isPartial then remaining.insert name else remaining
  let cancel ← IO.CancelToken.new
  let checks ← IO.mkRef #[]
  let rejection ← IO.mkRef none
  let awaitChecks := awaitChecks checks rejection
  let replayed ← try
      let (_, s) ← (do
          for n in remaining do replayConstant n
          checkPostponed : ReplayM Unit).run { newConstants, cancel, checks, rejection }
        |>.run { env, remaining }
      pure s.env
    catch ex =>
      cancel.set
      let sequential ← rejection.get
      discard awaitChecks
      if let some diagnostic := diagnostic then diagnostic.set sequential
      throw ex
  if let some failure ← awaitChecks then
    if let some diagnostic := diagnostic then diagnostic.set (← rejection.get)
    throw <| .userError failure
  return replayed

/-- Replays every target and exposes the checked environment while its imported regions live.
The callback flag excludes ambiguous ownership and duplicates whose selected proof body may differ.
The owner resolver identifies target and external declarations for request-local audit scopes.
The target owner map also enumerates every private, auxiliary and unused target declaration. -/
unsafe def withReplayedModules (args : List String)
    (checked : Lean.Kernel.Environment → Bool → (Lean.Name → Option Lean.Name) →
      Std.HashMap Lean.Name Lean.Name → IO Unit) :
    IO Unit := do
  let started ← IO.monoMsNow
  let names := args.map String.toName
  let targets : Lean.NameSet := names.foldl (·.insert ·) {}
  let mut imports : Std.HashMap Lean.Name Lean.Import := {}
  let mut constants : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  let mut owners : Std.HashMap Lean.Name Lean.Name := {}
  let mut extraOwners : Std.HashMap Lean.Name Lean.Name := {}
  let mut unique := true
  for module in names do
    let (exported, complete) ← readReplayParts module
    for name in complete.extraConstNames do
      if let some owner := extraOwners[name]? then
        if owner != module then unique := false
      extraOwners := extraOwners.insert name module
    for dependency in exported.imports do
      unless targets.contains dependency.module do
        imports := imports.insert dependency.module <| match imports[dependency.module]? with
          | some prior => { prior with
              importAll := prior.importAll || dependency.importAll
              isExported := prior.isExported || dependency.isExported
              isMeta := prior.isMeta || dependency.isMeta }
          | none => dependency
    -- The most private part subsumes the others.
    for name in complete.constNames, ci in complete.constants do
      match constants[name]? with
      | some prior =>
        unique := false
        unless sameReplayTheorem prior ci do
          throw <| IO.userError s!"Constant {name} is declared by more than one replay target"
      | none =>
        constants := constants.insert name ci
        owners := owners.insert name module
  let external := imports.toArray.map (·.2) |>.qsort (·.module.toString < ·.module.toString)
  let (_, s) ← Lean.importModulesCore external |>.run
  let env ← Lean.finalizeImport s external {} 0 false false (isModule := true)
  try
    let imported := env.allImportedModuleNames
    -- Same-module auxiliaries retain their owner. Conflicting entries need the imported
    -- catalog's ownership precedence instead of a synthesized fused ownership map.
    for (name, owner) in extraOwners do
      if let some declaredOwner := owners[name]? then
        if owner != declaredOwner then unique := false
      else if (env.find? name).isSome then unique := false
    for (name, ci) in constants do
      if let some prior := env.find? name then
        unique := false
        -- Only identical theorems from untargeted modules may be skipped, as in per-module replay.
        let owner := (env.getModuleIdxFor? name).bind (imported[·.toNat]?)
        unless owner.any (!targets.contains ·) && sameReplayTheorem prior ci do
          throw <| IO.userError s!"Replay target constant {name} is already imported"
    let replayed ← replay constants env.toKernelEnv
    let ownerOf := fun name => owners[name]? <|>
      ((env.getModuleIdxFor? name).bind (imported[·.toNat]?))
    checked replayed unique ownerOf owners
  finally env.freeRegions
  let elapsed := (← IO.monoMsNow) - started
  for name in args do
    IO.println (Lean.Json.mkObj [("module", Lean.toJson name), ("joint", Lean.toJson true),
      ("milliseconds", Lean.toJson elapsed)]).compress

/-- Replays every target declaration against shared dependencies without loading extensions. -/
unsafe def replayModulesJointly (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  withReplayedModules args fun _ _ _ _ => pure ()

/-- Replays one module with the pinned toolchain's `LeanChecker.replayFromImports` semantics.
Its imported environment is private to this module, including when another target fails. -/
unsafe def replayModuleSeparately (name : String) : IO Nat := do
  let started ← IO.monoMsNow
  let (exported, complete) ← readReplayParts name.toName
  let (_, state) ← Lean.importModulesCore exported.imports |>.run
  let env ← Lean.finalizeImport state exported.imports {} 0 false false (isModule := true)
  try
    let mut constants := {}
    for name in complete.constNames, ci in complete.constants do
      constants := constants.insert name ci
    discard <| env.toKernelEnv.replay constants
  finally env.freeRegions
  return (← IO.monoMsNow) - started

/-- Reports every independent module's kernel verdict without elaborating a runner source.
This uses sequential toolchain replay within each module, with independent modules in tasks. -/
unsafe def replayModulesSeparately (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let tasks ← args.toArray.mapM fun name => do
    return (name, ← IO.asTask (replayModuleSeparately name))
  let mut failed := false
  for (name, task) in tasks do
    let fields := [("module", Lean.toJson name)]
    match ← IO.wait task with
    | .ok elapsed =>
      IO.println (Lean.Json.mkObj (fields ++ [("milliseconds", Lean.toJson elapsed)])).compress
    | .error error =>
      IO.println (Lean.Json.mkObj (fields ++ [("error", Lean.toJson (toString error))])).compress
      failed := true
  return if failed then 1 else 0

/-- Stable protocol spellings for checking-boundary rejection kinds. -/
def RejectionKind.protocolName : RejectionKind → String
  | .unknownConstant => "unknownConstant"
  | .alreadyDeclared => "alreadyDeclared"
  | .declTypeMismatch => "declTypeMismatch"
  | .declHasMVars => "declHasMVars"
  | .declHasFVars => "declHasFVars"
  | .funExpected => "funExpected"
  | .typeExpected => "typeExpected"
  | .letTypeMismatch => "letTypeMismatch"
  | .exprTypeMismatch => "exprTypeMismatch"
  | .appTypeMismatch => "appTypeMismatch"
  | .invalidProj => "invalidProj"
  | .thmTypeIsNotProp => "thmTypeIsNotProp"
  | .constructorMismatch => "constructorMismatch"
  | .recursorMismatch => "recursorMismatch"

/-- Requires every complete declaration and mutual member to belong uniquely to this module. -/
unsafe def diagnosticConstants (complete : Lean.ModuleData) (env : Lean.Environment) :
    IO (Std.HashMap Lean.Name Lean.ConstantInfo) := do
  unless complete.constNames.size == complete.constants.size do
    throw <| IO.userError "Mismatched declaration inventory"
  let mut constants : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  for name in complete.constNames, info in complete.constants do
    if name.isAnonymous || name != info.name || constants.contains name ||
        (env.find? name).isSome then
      throw <| IO.userError s!"Ambiguous declaration ownership: {name}"
    constants := constants.insert name info
  let mut extra : Std.HashSet Lean.Name := {}
  for name in complete.extraConstNames do
    if extra.contains name || (env.find? name).isSome then
      throw <| IO.userError s!"Ambiguous auxiliary ownership: {name}"
    extra := extra.insert name
  -- Shared physical tails retain their validated ownership for this module inventory.
  let mut checked : Lean.PtrSet (List Lean.Name) := Lean.mkPtrSet
  for (_, info) in constants do
    let mut members := info.all
    while !members.isEmpty do
      if checked.contains members then break
      let member := members.head!
      unless constants.contains member do
        throw <| IO.userError s!"Unowned mutual declaration: {member}"
      checked := checked.insert members
      members := members.tail!
    if let .inductInfo inductiveInfo := info then
      for ctor in inductiveInfo.ctors do
        unless constants.contains ctor do
          throw <| IO.userError s!"Unowned constructor: {ctor}"
  return constants

/-- Diagnoses one module against precisely its exported imports and complete declaration part. -/
unsafe def diagnoseModule (name : String) : IO ReplayDiagnostic := do
  let operation : IO ReplayDiagnostic := do
    let (exported, complete) ← readReplayParts name.toName
    let (_, state) ← Lean.importModulesCore exported.imports |>.run
    let env ← Lean.finalizeImport state exported.imports {} 0 false false (isModule := true)
    let check : IO ReplayDiagnostic := do
      let constants ← diagnosticConstants complete env
      let rejection ← IO.mkRef none
      try
        discard <| replay constants env.toKernelEnv (some rejection)
        return .accepted
      catch error =>
        if let some rejected ← rejection.get then
          if constants.contains rejected.declaration then return .rejected rejected
        return .unavailable (toString error)
    try check
    finally env.freeRegions
  try operation
  catch error => return .unavailable (toString error)

/-- Emits one strict diagnostic record for each unique target and a terminal completion record. -/
unsafe def diagnoseModules (targets : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let mut seen : Std.HashSet String := {}
  for target in targets do
    if target.isEmpty || seen.contains target then
      throw <| IO.userError "Diagnostic targets must be unique nonempty names"
    seen := seen.insert target
  for target in targets do
    let outcome ← diagnoseModule target
    let fields := [("module", Lean.toJson target)]
    let result := match outcome with
      | .accepted => [("outcome", Lean.toJson "accepted")]
      | .unavailable message => [("outcome", Lean.toJson "unavailable"),
          ("error", Lean.toJson message)]
      | .rejected rejection => [("outcome", Lean.toJson "rejected"),
          ("declaration", Lean.toJson rejection.declaration.toString),
          ("kind", Lean.toJson rejection.kind.protocolName)]
    IO.println (Lean.Json.mkObj (fields ++ result)).compress
  IO.println (Lean.Json.mkObj [("complete", Lean.toJson true)]).compress
  return 0

end CIL.Replay
