import CIL.Replay

/-! Typed replay classifications preserve resource failures and join every deferred task. -/

open CIL.Replay

/-- Resource and generic failures cannot identify a semantic rejection. -/
def excluded : IO Unit := do
  for error in [Lean.Kernel.Exception.other "type mismatch", .deterministicTimeout,
      .excessiveMemory, .deepRecursion, .interrupted] do
    unless (rejectionKind error).isNone do throw <| IO.userError "Resource misclassified"

#eval excluded

/-- Every approved kernel exception constructor retains its distinct typed category. -/
def included : IO Unit := do
  let environment ← Lean.mkEmptyEnvironment
  let env := environment.toKernelEnv
  let expression := Lean.mkSort .zero
  let declaration := Lean.Declaration.axiomDecl
    { name := `Test, levelParams := [], type := expression, isUnsafe := false }
  let cases : List (Lean.Kernel.Exception × RejectionKind) := [
    (.unknownConstant env `Test, .unknownConstant),
    (.alreadyDeclared env `Test, .alreadyDeclared),
    (.declTypeMismatch env declaration expression, .declTypeMismatch),
    (.declHasMVars env `Test expression, .declHasMVars),
    (.declHasFVars env `Test expression, .declHasFVars),
    (.funExpected env {} expression, .funExpected),
    (.typeExpected env {} expression, .typeExpected),
    (.letTypeMismatch env {} `Test expression expression, .letTypeMismatch),
    (.exprTypeMismatch env {} expression expression, .exprTypeMismatch),
    (.appTypeMismatch env {} expression expression expression, .appTypeMismatch),
    (.invalidProj env {} expression, .invalidProj),
    (.thmTypeIsNotProp env `Test expression, .thmTypeIsNotProp)]
  for (error, expected) in cases do
    unless rejectionKind error == some expected do throw <| IO.userError "Kernel category lost"

#eval included

/-- An earlier unavailable check defeats a later semantic result, and every task is joined. -/
def unavailableFirst : IO Unit := do
  for first in [Except.error (IO.userError "rendering failed"),
      Except.ok (CheckOutcome.rejected "resource exhausted" none)] do
    let finished ← IO.mkRef false
    let check ← IO.asTask do
      finished.set true
      return CheckOutcome.rejected "bad theorem" (some .declTypeMismatch)
    let checks ← IO.mkRef #[(`first, Task.pure first), (`second, check)]
    let rejection ← IO.mkRef none
    unless (← awaitChecks checks rejection).isSome && (← rejection.get).isNone &&
        (← finished.get) do
      throw <| IO.userError "Unavailable first result or task join lost"

#eval unavailableFirst

/-- Cancellation alone supplies no semantic rejection classification. -/
def cancellation : IO Unit := do
  let checks ← IO.mkRef #[(`cancelled, Task.pure (.ok CheckOutcome.cancelled))]
  let rejection ← IO.mkRef none
  discard <| awaitChecks checks rejection
  unless (← rejection.get).isNone do throw <| IO.userError "Cancellation misclassified"

#eval cancellation

/-- Sequential kernel failures carry a kind; missing postponed records remain unavailable. -/
def sequentialChecks : IO Unit := do
  let env ← Lean.mkEmptyEnvironment
  let cancel ← IO.CancelToken.new
  let checks ← IO.mkRef #[]
  let rejection ← IO.mkRef none
  let context : ReplayContext := { newConstants := {}, cancel, checks, rejection }
  let declaration := Lean.Declaration.inductDecl [] 0
    [{ name := `Broken, type := Lean.mkConst `Missing, ctors := [] }] false
  let mut failed := false
  try
    discard <| (addDecl declaration).run context |>.run { env := env.toKernelEnv }
  catch _ => failed := true
  unless failed && (← rejection.get).any (·.kind == .unknownConstant) do
    throw <| IO.userError "Sequential rejection lost"
  rejection.set none
  try
    discard <| checkPostponed.run context |>.run
      { env := env.toKernelEnv, postponedConstructors := ({} : Lean.NameSet).insert `Missing }
  catch _ => pure ()
  unless (← rejection.get).isNone do throw <| IO.userError "Missing record misclassified"

#eval sequentialChecks

/-- A malformed sequential block keeps deferred semantic failures unavailable. -/
def sequentialUnavailable : IO Unit := do
  let environment ← Lean.mkEmptyEnvironment
  let badProof : Lean.TheoremVal := {
    name := `Dependency, levelParams := [], type := Lean.mkSort .zero, value := Lean.mkSort .zero }
  let cancel ← IO.CancelToken.new
  match ← checkDeclaration environment.toKernelEnv (.thmDecl badProof) cancel with
  | .rejected _ (some _) => pure ()
  | _ => throw <| IO.userError "Expected a semantic deferred failure"
  let malformed : Lean.InductiveVal := { (default : Lean.InductiveVal) with
    name := `Block, type := Lean.mkConst `Dependency, all := [`Missing] }
  let constants : Std.HashMap Lean.Name Lean.ConstantInfo :=
    ({} : Std.HashMap Lean.Name Lean.ConstantInfo)
      |>.insert `Block (.inductInfo malformed) |>.insert `Dependency (.thmInfo badProof)
  let rejection ← IO.mkRef none
  let mut failed := false
  try discard <| replay constants environment.toKernelEnv (some rejection)
  catch _ => failed := true
  unless failed && (← rejection.get).isNone do
    throw <| IO.userError "Sequential unavailability was overwritten by a deferred rejection"

#eval sequentialUnavailable

/-- Constructor and recursor mismatches require both records with the expected kind. -/
def postponedChecks : IO Unit := do
  let env ← Lean.mkEmptyEnvironment
  let declaration := Lean.Declaration.inductDecl [] 0
    [{ name := `Single, type := Lean.mkSort (.succ .zero),
       ctors := [{ name := `Single.mk, type := Lean.mkConst `Single }] }] false
  let kernel ← match env.toKernelEnv.addDeclCore 0 0 declaration none with
    | .ok kernel => pure kernel
    | .error error => throw <| IO.userError (← kernelMessage error)
  let some (.ctorInfo ctor) := kernel.find? `Single.mk
    | throw <| IO.userError "Missing generated constructor"
  let some (.recInfo recursor) := kernel.find? `Single.rec
    | throw <| IO.userError "Missing generated recursor"
  let cases := #[(Lean.ConstantInfo.ctorInfo { ctor with numFields := ctor.numFields + 1 },
      RejectionKind.constructorMismatch),
    (Lean.ConstantInfo.recInfo { recursor with numMinors := recursor.numMinors + 1 },
      RejectionKind.recursorMismatch)]
  for (info, expected) in cases do
    let cancel ← IO.CancelToken.new
    let checks ← IO.mkRef #[]
    let rejection ← IO.mkRef none
    let context : ReplayContext :=
      { newConstants := ({} : Std.HashMap Lean.Name Lean.ConstantInfo).insert info.name info,
        cancel, checks, rejection }
    let names := ({} : Lean.NameSet).insert info.name
    let state : ReplayState := {
      env := kernel
      postponedConstructors := (if expected == .constructorMismatch then names else {})
      postponedRecursors := (if expected == .recursorMismatch then names else {}) }
    try discard <| checkPostponed.run context |>.run state
    catch _ => pure ()
    unless (← rejection.get).any (·.kind == expected) do
      throw <| IO.userError "Postponed mismatch lost"

#eval postponedChecks

/-- Ownership rejects duplicate names, missing mutual members and imported declarations. -/
unsafe def ownership : IO Unit := do
  let env ← Lean.mkEmptyEnvironment
  let info : Lean.ConstantInfo := .axiomInfo
    { name := `Owned, levelParams := [], type := Lean.mkSort .zero, isUnsafe := false }
  let base : Lean.ModuleData :=
    { (default : Lean.ModuleData) with constNames := #[info.name], constants := #[info] }
  discard <| diagnosticConstants base env
  let mutualInfo : Lean.ConstantInfo := .thmInfo {
    name := `Owned, levelParams := [], type := Lean.mkSort .zero,
    value := Lean.mkSort .zero, all := [`Unowned] }
  let ownedDeclaration := Lean.Declaration.axiomDecl
    { name := `Owned, levelParams := [], type := Lean.mkSort .zero, isUnsafe := false }
  let imported ← match env.addDeclCore 0 0 ownedDeclaration none with
    | .ok imported => pure imported
    | .error error => throw <| IO.userError (← kernelMessage error)
  for (data, environment) in #[(base, imported),
      ({ base with constNames := #[`Owned, `Owned], constants := #[info, info] }, env),
      ({ base with constNames := #[`Other] }, env),
      ({ base with constNames := #[] }, env),
      ({ base with extraConstNames := #[`Extra, `Extra] }, env),
      ({ base with constants := #[mutualInfo] }, env)] do
    let mut failed := false
    try discard <| diagnosticConstants data environment
    catch _ => failed := true
    unless failed do throw <| IO.userError "Ambiguous ownership accepted"

#eval ownership

/-- The owner index grows with the declaration inventory, without per-declaration rescans. -/
unsafe def ownershipScaling : IO Unit := do
  let env ← Lean.mkEmptyEnvironment
  let mut previous := 0
  for count in [64, 256, 1024] do
    let constants := (List.range count).toArray.map fun index =>
      Lean.ConstantInfo.axiomInfo {
        name := .num `Owned index, levelParams := []
        type := Lean.mkSort .zero, isUnsafe := false }
    let data : Lean.ModuleData := { (default : Lean.ModuleData) with
      constNames := constants.map (·.name), constants }
    discard <| diagnosticConstants data env
    let before ← IO.getNumHeartbeats
    discard <| diagnosticConstants data env
    let used := (← IO.getNumHeartbeats) - before
    if previous > 0 && used > previous * 6 then
      throw <| IO.userError "Owner inventory grew faster than its linear bound"
    IO.println s!"Owner inventory {count}: {used} heartbeats"
    previous := used

#eval ownershipScaling

/-- Shared complete mutual lists require work proportional to their distinct physical cells. -/
unsafe def mutualOwnershipScaling : IO Unit := do
  let env ← Lean.mkEmptyEnvironment
  let mut previous := 0
  for count in [64, 256, 1024] do
    let names := (List.range count).map (Lean.Name.num `Mutual)
    let constants := names.toArray.map fun name =>
      Lean.ConstantInfo.thmInfo {
        name, levelParams := [], type := Lean.mkSort .zero,
        value := Lean.mkSort .zero, all := names }
    let data : Lean.ModuleData := { (default : Lean.ModuleData) with
      constNames := names.toArray, constants }
    discard <| diagnosticConstants data env
    let before ← IO.getNumHeartbeats
    discard <| diagnosticConstants data env
    let used := (← IO.getNumHeartbeats) - before
    if previous > 0 && used > previous * 6 then
      throw <| IO.userError "Shared mutual inventory grew faster than its linear bound"
    IO.println s!"Shared mutual inventory {count}: {used} heartbeats"
    previous := used

#eval mutualOwnershipScaling

/-- Equal heads with physically divergent tails do not share ownership validation. -/
unsafe def divergentOwnership : IO Unit := do
  let env ← Lean.mkEmptyEnvironment
  for reverse in [false, true] do
    let owned : Lean.ConstantInfo := .thmInfo {
      name := `Owned, levelParams := [], type := Lean.mkSort .zero,
      value := Lean.mkSort .zero, all := [`Owned, `Other] }
    let divergent : Lean.ConstantInfo := .thmInfo {
      name := `Other, levelParams := [], type := Lean.mkSort .zero,
      value := Lean.mkSort .zero, all := [`Owned, `Unowned] }
    let constants := if reverse then #[divergent, owned] else #[owned, divergent]
    let data : Lean.ModuleData := { (default : Lean.ModuleData) with
      constNames := constants.map (·.name), constants }
    let mut failed := false
    try discard <| diagnosticConstants data env
    catch _ => failed := true
    unless failed do throw <| IO.userError "Divergent unowned mutual tail accepted"

#eval divergentOwnership
