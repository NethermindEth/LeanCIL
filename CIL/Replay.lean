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

/-- Replays every target declaration against shared dependencies without loading extensions. -/
unsafe def replayModulesJointly (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let started ← IO.monoMsNow
  let names := args.map String.toName
  let targets : Lean.NameSet := names.foldl (·.insert ·) {}
  let mut imports : Std.HashMap Lean.Name Lean.Import := {}
  let mut constants : Std.HashMap Lean.Name Lean.ConstantInfo := {}
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
        unless sameReplayTheorem prior ci do
          throw <| IO.userError s!"Constant {name} is declared by more than one replay target"
      | none => constants := constants.insert name ci
  let external := imports.toArray.map (·.2) |>.qsort (·.module.toString < ·.module.toString)
  let (_, s) ← Lean.importModulesCore external |>.run
  let env ← Lean.finalizeImport s external {} 0 false false (isModule := true)
  let imported := env.allImportedModuleNames
  for (name, ci) in constants do
    if let some prior := env.find? name then
      -- Only identical theorems from untargeted modules may be skipped, as in per-module replay.
      let owner := (env.getModuleIdxFor? name).bind (imported[·.toNat]?)
      unless owner.any (!targets.contains ·) && sameReplayTheorem prior ci do
        throw <| IO.userError s!"Replay target constant {name} is already imported"
  discard <| env.toKernelEnv.replay constants
  env.freeRegions
  let elapsed := (← IO.monoMsNow) - started
  for name in args do
    IO.println (Lean.Json.mkObj [("module", Lean.toJson name), ("joint", Lean.toJson true),
      ("milliseconds", Lean.toJson elapsed)]).compress

end CIL.Replay

