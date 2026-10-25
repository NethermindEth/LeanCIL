import Proof

/-! Per-declaration kernel checking for the fixed issue #270 consumer proof closure. -/

open Lean in
run_cmd do
  let environment ← getEnv
  let measuredModules := environment.allImportedModuleNames.toList.filter fun name =>
    name.toString.startsWith "UInt256" || name == `Extracted || name == `Proof
  let mut count : Nat := 0
  let mut totalHeartbeats : Nat := 0
  let mut totalMilliseconds : Nat := 0
  for moduleName in measuredModules do
    logInfo m!"TARGET {moduleName}"
    let some moduleIndex := environment.getModuleIdx? moduleName |
      throwError "Missing measured module {moduleName}"
    let mut moduleCount : Nat := 0
    let mut moduleHeartbeats : Nat := 0
    let mut moduleMilliseconds : Nat := 0
    for (name, info) in environment.constants.toList do
      unless environment.getModuleIdxFor? name == some moduleIndex do continue
      let .thmInfo declaration := info | continue
      let checked := Expr.letE `measured declaration.type declaration.value (.bvar 0) false
      let start ← IO.monoMsNow
      let heartbeats ← IO.getNumHeartbeats
      match Kernel.check environment {} checked with
      | .error _ => throwError "Kernel rejected {name}"
      | .ok _ =>
        let used := (← IO.getNumHeartbeats) - heartbeats
        let elapsed := (← IO.monoMsNow) - start
        moduleCount := moduleCount + 1
        moduleHeartbeats := moduleHeartbeats + used
        moduleMilliseconds := moduleMilliseconds + elapsed
        logInfo m!"{name}: {elapsed} ms; {used} raw heartbeats"
    count := count + moduleCount
    totalHeartbeats := totalHeartbeats + moduleHeartbeats
    totalMilliseconds := totalMilliseconds + moduleMilliseconds
    logInfo <| m!"MODULE {moduleName}: {moduleCount} theorems; " ++
      m!"{moduleMilliseconds} ms; {moduleHeartbeats} raw heartbeats"
  logInfo m!"TOTAL {count} theorems: {totalMilliseconds} ms; {totalHeartbeats} raw heartbeats"
