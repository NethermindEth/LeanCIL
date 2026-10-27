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

/-- Kernel verdict for one deferred declaration check. -/
inductive CheckOutcome where
  | accepted
  | cancelled
  | rejected (message : String)

/-- Constants being replayed and the deferred checks issued so far. -/
structure ReplayContext where
  newConstants : Std.HashMap Lean.Name Lean.ConstantInfo
  cancel : IO.CancelToken
  checks : IO.Ref (Array (Lean.Name × Task (Except IO.Error CheckOutcome)))

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

/-- Adds a declaration; a deferred check sees only the declarations added before it. -/
def addDecl (decl : Lean.Declaration) : ReplayM Unit := do
  let before := (← get).env
  match decl with
  | .defnDecl _ | .thmDecl _ | .opaqueDecl _ | .axiomDecl _ =>
    match before.addDeclWithoutChecking decl with
    | .error ex => throw <| .userError (← kernelMessage ex)
    | .ok env =>
      let cancel := (← read).cancel
      let check ← IO.asTask do
        match before.addDeclCore 0 0 decl (some cancel) with
        | .ok _ => return CheckOutcome.accepted
        | .error .interrupted => return .cancelled
        | .error ex =>
          cancel.set
          return .rejected (← kernelMessage ex)
      let name := decl.getNames.headD .anonymous
      (← read).checks.modify (·.push (name, check))
      modify fun s => { s with env }
  | _ =>
    match before.addDeclCore 0 0 decl (cancelTk? := none) with
    | .ok env => modify fun s => { s with env }
    | .error ex => throw <| .userError (← kernelMessage ex)

mutual
/-- Replays the constants a pending name uses, then the name itself. -/
partial def replayConstant (name : Lean.Name) : ReplayM Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
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
          let all ← info.all.mapM fun n => do pure (← read).newConstants[n]!
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do pure (← read).newConstants[n]!)
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
      if !(info == info') then throw <| .userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| .userError s!"No such constructor {ctor}"
  for recursor in (← get).postponedRecursors do
    match (← get).env.find? recursor, (← read).newConstants[recursor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if !(info == info') then throw <| .userError s!"Invalid recursor {recursor}"
    | _, _ => throw <| .userError s!"No such recursor {recursor}"

/-- Kernel-checks every safe, total constant into `env`, accepting exactly what sequential replay
accepts.
Every deferred check has finished when this returns or throws, so imported regions may be freed. -/
def replay (newConstants : Std.HashMap Lean.Name Lean.ConstantInfo)
    (env : Lean.Kernel.Environment) : IO Lean.Kernel.Environment := do
  let remaining := newConstants.fold (init := {}) fun remaining name ci =>
    if !ci.isUnsafe && !ci.isPartial then remaining.insert name else remaining
  let cancel ← IO.CancelToken.new
  let checks ← IO.mkRef #[]
  let awaitChecks : IO (Option String) := do
    let mut failure := none
    for (name, check) in ← checks.get do
      match ← IO.wait check with
      | .ok (.rejected message) =>
        failure := failure <|> some s!"while replaying declaration '{name}':\n{message}"
      | .ok _ => pure ()
      | .error ex => failure := failure <|> some s!"while replaying declaration '{name}':\n{ex}"
    return failure
  let replayed ← try
      let (_, s) ← (do
          for n in remaining do replayConstant n
          checkPostponed : ReplayM Unit).run { newConstants, cancel, checks }
        |>.run { env, remaining }
      pure s.env
    catch ex =>
      cancel.set
      discard awaitChecks
      throw ex
  if let some failure ← awaitChecks then throw <| .userError failure
  return replayed

/-- Replays every target and exposes the checked environment while its imported regions live.
The callback flag excludes duplicate declarations whose selected proof body may differ.
The owner resolver identifies target and external declarations for request-local audit scopes. -/
unsafe def withReplayedModules (args : List String)
    (checked : Lean.Kernel.Environment → Bool → (Lean.Name → Option Lean.Name) → IO Unit) :
    IO Unit := do
  let started ← IO.monoMsNow
  let names := args.map String.toName
  let targets : Lean.NameSet := names.foldl (·.insert ·) {}
  let mut imports : Std.HashMap Lean.Name Lean.Import := {}
  let mut constants : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  let mut owners : Std.HashMap Lean.Name Lean.Name := {}
  let mut unique := true
  for module in names do
    let (exported, complete) ← readReplayParts module
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
    checked replayed unique ownerOf
  finally env.freeRegions
  let elapsed := (← IO.monoMsNow) - started
  for name in args do
    IO.println (Lean.Json.mkObj [("module", Lean.toJson name), ("joint", Lean.toJson true),
      ("milliseconds", Lean.toJson elapsed)]).compress

/-- Replays every target declaration against shared dependencies without loading extensions. -/
unsafe def replayModulesJointly (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  withReplayedModules args fun _ _ _ => pure ()

end CIL.Replay
