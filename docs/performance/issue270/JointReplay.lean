import LeanChecker

/-! Independent joint replay of the fixed consumer and extraction modules for issue #270. -/
/-- Read the complete private object part used by independent kernel replay. -/
unsafe def readReplayParts (module : Lean.Name) : IO (Lean.ModuleData × Lean.ModuleData) := do
  let mFile ← Lean.findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := Lean.OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := Lean.OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← Lean.readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  return (parts[0].1, parts[parts.size-1].1)
/-- Admit only the identical equation theorem duplicates allowed by Lean import/replay. -/
def sameReplayTheorem : Lean.ConstantInfo → Lean.ConstantInfo → Bool
  | .thmInfo left, .thmInfo right =>
    left.name == right.name && left.type == right.type &&
      left.levelParams == right.levelParams && left.all == right.all
  | _, _ => false
/-- Replay all target declarations without importing any target module as trusted evidence. -/
unsafe def replayModulesJointly (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let started ← IO.monoMsNow
  let names := args.map String.toName
  let targets : Lean.NameSet := names.foldl (·.insert ·) {}
  let mut imports : Std.HashMap Lean.Name Lean.Import := {}
  let mut constants : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  for module in names do
    let (exported, complete) ← readReplayParts module
    for i in exported.imports do
      unless targets.contains i.module do
        imports := imports.insert i.module <| match imports[i.module]? with
          | some prior => { prior with
              importAll := prior.importAll || i.importAll
              isExported := prior.isExported || i.isExported
              isMeta := prior.isMeta || i.isMeta }
          | none => i
    -- The most private part subsumes the others.
    for name in complete.constNames, ci in complete.constants do
      match constants[name]? with
      | some prior =>
        unless sameReplayTheorem prior ci do
          throw <| IO.userError s!"Constant {name} is declared by more than one replay target"
      | none => constants := constants.insert name ci
  let external := imports.toArray.map (·.2) |>.qsort (·.module.toString < ·.module.toString)
  let (_, s) ← Lean.importModulesCore external |>.run
  let env ← Lean.finalizeImport s external {} 0 false false (isModule := true)
  let imported := env.allImportedModuleNames
  for (name, ci) in constants do
    if let some prior := env.find? name then
      -- Per-module replay permits only identical theorems from untargeted modules.
      let owner := (env.getModuleIdxFor? name).bind (imported[·.toNat]?)
      unless owner.any (!targets.contains ·) && sameReplayTheorem prior ci do
        throw <| IO.userError s!"Replay target constant {name} is already imported"
  let before ← IO.getNumHeartbeats
  discard <| env.toKernelEnv.replay constants
  let heartbeats := (← IO.getNumHeartbeats) - before
  IO.println <| s!"REPLAY {names.length} modules; {constants.size} declarations; " ++
    s!"{heartbeats} raw heartbeats"
  env.freeRegions
  let elapsed := (← IO.monoMsNow) - started
  for name in args do
    IO.println (Lean.Json.mkObj [
      ("module", Lean.toJson name), ("joint", Lean.toJson true),
      ("milliseconds", Lean.toJson elapsed)]).compress
#eval do
  let text ← IO.FS.readFile "ReplayTargets.json"
  let targets ← IO.ofExcept <| (Lean.Json.parse text).bind Lean.fromJson?
  replayModulesJointly targets