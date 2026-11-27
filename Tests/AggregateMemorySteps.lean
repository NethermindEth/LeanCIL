import CIL.Safety.AggregateMemorySteps
import CIL.Safety.MethodContract

/-!
# Aggregate operation facts

Checked aggregate steps consume byte or snapshot operations, as one checked step and as one
contract step. Unknown bytes retain their flags; access authority, an old snapshot and a mismatched
width cannot supply the missing contents.
-/

namespace Tests.AggregateMemorySteps
open CIL.Safety

/-- Initialized bytes load as an ordinary aggregate. -/
theorem initialized_load {memory : Memory} {source : Reference} {width : Nat}
    {bytes : List (BitVec 8)} (loaded : read memory source width 1 = .ok bytes)
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate width)
    (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.ldobj type) pc args frame (.reference (.address source) :: rest)
      memory = .ok (.next (pc + 1) (.scalar (.aggregate bytes) :: rest) frame memory) := by
  cil_checked_step [shape, loaded]
#print axioms initialized_load

/-- Readonly loads preserve the same initialized byte evidence. -/
theorem readonly_load {memory : Memory} {source : Reference} {width : Nat}
    {bytes : List (BitVec 8)} (loaded : read memory source width 1 = .ok bytes)
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate width)
    (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.ldobj type) pc args frame (.readOnlyReference (.address source) :: rest)
      memory = .ok (.next (pc + 1) (.scalar (.aggregate bytes) :: rest) frame memory) := by
  cil_checked_step [shape, loaded]
#print axioms readonly_load

/-- A read stated at a local kind's width, as a remembered aggregate local gives it, supplies
    the load at the numeral width the opcode carries. -/
theorem kind_width_load {memory : Memory} {source : Reference} {bytes : List (BitVec 8)}
    (loaded : read memory source (localWidth (.aggregate 32)) 1 = .ok bytes)
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate 32)
    (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.ldobj type) pc args frame (.reference (.address source) :: rest)
      memory = .ok (.next (pc + 1) (.scalar (.aggregate bytes) :: rest) frame memory) := by
  cil_checked_step [shape, loaded]
#print axioms kind_width_load

/-- One contract step derives the aggregate load from a supplied read, as a checked step does,
    so a walk taken one step at a time crosses a load through a managed-reference address. -/
theorem contract_step_load {memory : Memory} {source : Reference} {bytes : List (BitVec 8)}
    (loaded : read memory source 32 1 = .ok bytes)
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate 32) (program : CIL.Program) (method : Nat)
    (found : program[method]? = some body)
    (instruction : body.code[0]? = some (.ldobj type)) (frame : Frame) (rest : List Value)
    (continuation : WP (Execution (fun fuel => run program fuel method 1 [] frame
      (.scalar (.aggregate bytes) :: rest) memory)) (fun _ => True)) :
    WP (Execution (fun fuel => run program fuel method 0 [] frame
      (.reference (.address source) :: rest) memory)) (fun _ => True) := by
  cil_contract_prepare []
  -- The read is no step fact until it is prepared, so the unprepared step stops here.
  fail_if_success cil_contract_step_normalized [shape, found, instruction, loaded]
  cil_contract_step [shape, found, instruction, loaded]
  exact WP.adequate.mp continuation
#print axioms contract_step_load

/-- The contract step also takes the read at a local kind's width, as a remembered aggregate
    local states it. -/
theorem contract_step_kind_width_load {memory : Memory} {source : Reference}
    {bytes : List (BitVec 8)}
    (loaded : read memory source (localWidth (.aggregate 32)) 1 = .ok bytes)
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate 32) (program : CIL.Program) (method : Nat)
    (found : program[method]? = some body)
    (instruction : body.code[0]? = some (.ldobj type)) (frame : Frame) (rest : List Value)
    (continuation : WP (Execution (fun fuel => run program fuel method 1 [] frame
      (.scalar (.aggregate bytes) :: rest) memory)) (fun _ => True)) :
    WP (Execution (fun fuel => run program fuel method 0 [] frame
      (.readOnlyReference (.address source) :: rest) memory)) (fun _ => True) := by
  cil_contract_prepare []
  cil_contract_step [shape, found, instruction, loaded]
  exact WP.adequate.mp continuation
#print axioms contract_step_kind_width_load

/-- A walk derives the load from a read restated by `have`, whose type is inferred, at the
    width of a local kind: the width is evaluated to the numeral the opcode carries. -/
theorem contract_walk_restated_kind_load {memory : Memory} {source : Reference}
    {bytes : List (BitVec 8)}
    (loaded : read memory source (localWidth (.aggregate 32)) 1 = .ok bytes)
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate 32) (program : CIL.Program) (method : Nat)
    (found : program[method]? = some body)
    (instruction : body.code[0]? = some (.ldobj type)) (frame : Frame) (rest : List Value)
    (continuation : WP (Execution (fun fuel => run program fuel method 1 [] frame
      (.scalar (.aggregate bytes) :: rest) memory)) (fun _ => True)) :
    WP (Execution (fun fuel => run program fuel method 0 [] frame
      (.reference (.address source) :: rest) memory)) (fun _ => True) := by
  have restated := loaded
  clear loaded
  cil_contract_steps [shape, found, instruction, restated] until continuation
#print axioms contract_walk_restated_kind_load

/-- The same walk takes a restated read at the numeral width. -/
theorem contract_walk_restated_load {memory : Memory} {source : Reference}
    {bytes : List (BitVec 8)} (loaded : read memory source 32 1 = .ok bytes)
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate 32) (program : CIL.Program) (method : Nat)
    (found : program[method]? = some body)
    (instruction : body.code[0]? = some (.ldobj type)) (frame : Frame) (rest : List Value)
    (continuation : WP (Execution (fun fuel => run program fuel method 1 [] frame
      (.scalar (.aggregate bytes) :: rest) memory)) (fun _ => True)) :
    WP (Execution (fun fuel => run program fuel method 0 [] frame
      (.reference (.address source) :: rest) memory)) (fun _ => True) := by
  have restated := loaded
  clear loaded
  cil_contract_steps [shape, found, instruction, restated] until continuation
#print axioms contract_walk_restated_load

/-- An unknown byte loads as a snapshot without becoming initialized. -/
theorem unknown_load {memory : Memory} {source : Reference}
    (loaded : readSnapshot memory source 1 1 = .ok [(0, false)])
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate 1)
    (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.ldobj type) pc args frame (.reference (.address source) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.snapshot (.aggregate 1) [(0, false)]) :: rest)
        frame memory) := by
  cil_checked_step [shape, loaded]
#print axioms unknown_load

/-- Readonly aggregate loads also retain an unknown byte's initialization flag. -/
theorem readonly_unknown_load {memory : Memory} {source : Reference}
    (loaded : readSnapshot memory source 1 1 = .ok [(0, false)])
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate 1)
    (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.ldobj type) pc args frame (.readOnlyReference (.address source) :: rest)
      memory = .ok (.next (pc + 1)
        (.scalar (.snapshot (.aggregate 1) [(0, false)]) :: rest) frame memory) := by
  cil_checked_step [shape, loaded]
#print axioms readonly_unknown_load

/-- A symbolic snapshot preserves all its flags when at least one byte is unknown. -/
theorem symbolic_unknown_load {memory : Memory} {source : Reference} {width : Nat}
    {bytes : List (BitVec 8 × Bool)} (loaded : readSnapshot memory source width 1 = .ok bytes)
    (unknown : bytes.all Prod.snd = false)
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate width)
    (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.ldobj type) pc args frame (.reference (.address source) :: rest)
      memory = .ok (.next (pc + 1) (.scalar (.snapshot (.aggregate width) bytes) :: rest)
        frame memory) := by
  cil_checked_step [shape, loaded, unknown]
#print axioms symbolic_unknown_load

/-- A store uses the checked byte write and does not need old destination contents. -/
theorem initialized_store {memory after : Memory} {destination : Reference}
    {bytes : List (BitVec 8)} (written : write memory destination bytes 1 = .ok after)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value)
    {type : CIL.Extraction.TypeExpr} (shape : body.valueShape type = .aggregate bytes.length) :
    step body (.stobj type) pc args frame
      (.scalar (.aggregate bytes) :: .reference (.address destination) :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  cil_checked_step [shape, written]
#print axioms initialized_store

/-- Storing unknown bytes uses the snapshot write, which retains their initialization flags. -/
theorem unknown_store {memory after : Memory} {destination : Reference}
    (written : writeSnapshot memory destination [(0, false)] 1 = .ok after)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value)
    {type : CIL.Extraction.TypeExpr} (shape : body.valueShape type = .aggregate 1) :
    step body (.stobj type) pc args frame
      (.scalar (.snapshot (.aggregate 1) [(0, false)]) ::
        .reference (.address destination) :: rest) memory =
      .ok (.next (pc + 1) rest frame after) := by
  cil_checked_step [shape, written]
#print axioms unknown_store

/-- An unknown snapshot cannot be reported as an initialized aggregate. -/
theorem unknown_is_not_initialized {memory : Memory} {source : Reference}
    (loaded : readSnapshot memory source 1 1 = .ok [(0, false)])
    (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate 1)
    (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value) :
    step body (.ldobj type) pc args frame (.reference (.address source) :: rest) memory ≠
      .ok (.next (pc + 1) (.scalar (.aggregate [0]) :: rest) frame memory) := by
  rw [unknown_load loaded body shape]
  simp
#print axioms unknown_is_not_initialized

/-- A snapshot with the wrong shape width is rejected before its write operation. -/
theorem wrong_snapshot_width (memory : Memory) (destination : Reference)
    (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (rest : List Value)
    {type : CIL.Extraction.TypeExpr} (shape : body.valueShape type = .aggregate 1) :
    step body (.stobj type) pc args frame
      (.scalar (.snapshot (.aggregate 2) [(0, false)]) ::
        .reference (.address destination) :: rest) memory = .error .invalidState := by
  cil_checked_step [shape]
#print axioms wrong_snapshot_width

/-- A null aggregate load preserves the requested width in its fault. -/
theorem null_load_width (memory : Memory) (body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : body.valueShape type = .aggregate 8)
    (pc : Nat) (args : List Value)
    (frame : Frame) (rest : List Value) :
    step body (.ldobj type) pc args frame (.reference .null :: rest) memory =
      .error (.memory .nullDereference .null 8) := by
  cil_checked_step [shape]
#print axioms null_load_width

/-- Read authority alone cannot prove any particular loaded aggregate. -/
theorem access_does_not_supply_contents (memory : Memory) (source : Reference)
    (_readable : access memory source 1 1 false = .ok ())
    (_body : CIL.Method) {type : CIL.Extraction.TypeExpr}
    (shape : _body.valueShape type = .aggregate 1)
    (_pc : Nat) (_args : List Value) (_frame : Frame) (_rest : List Value) :
    True := by
  fail_if_success
    have : step _body (.ldobj type) _pc _args _frame
        (.reference (.address source) :: _rest) memory =
        .ok (.next (_pc + 1) (.scalar (.aggregate [0]) :: _rest) _frame memory) := by
      cil_checked_step [shape, _readable]
  trivial
#print axioms access_does_not_supply_contents

namespace WriteReadback

/-- A readable and writable range with one leading byte outside the store. -/
private def memory (width : Nat) : Memory := { Memory.empty with
  allocations := fun id => if id == 0 then
    some (.mk .callerStack (.mk (width + 1) 1 []) true []) else none
  views := [.mk 0 0 (width + 1) true true]
  nextIdentity := 1 }

/-- The bytes change within each block and across the byte index rollover. -/
private def payload (width : Nat) : List (BitVec 8) :=
  (List.range width).map fun index => BitVec.ofNat 8 (index + index / 256)

/-- A checked store and load of the same initialized aggregate through a nonzero offset. -/
private def Stepped (width : Nat) : Prop :=
  let target : Reference := ⟨0, 1⟩
  let type := CIL.Extraction.TypeExpr.aggregate "Fixture::Bytes" 0
  let raw : CIL.Extraction.RawLayout :=
    { identity := "Fixture::Bytes", explicit := true, packing := 1, declaredSize := width,
      fields := [] }
  let body : CIL.Method :=
    { code := [.stobj type, .ldobj type], locals := [], returnsValue := false
      environment := { rawLayouts := [raw], layouts := #[⟨{ size := width, fields := [] }, 1⟩] } }
  let frame := Frame.mk 0 [] [] 0 []
  let address := Value.reference (.address target)
  let bytes := payload width
  let value := Value.scalar (.aggregate bytes)
  let stored := (write (memory width) target bytes 1).toOption.getD Memory.empty
  step body (.stobj type) 0 [] frame [value, address] (memory width) =
      .ok (.next 1 [] frame stored) ∧
    step body (.ldobj type) 1 [] frame [address] stored =
      .ok (.next 2 [value] frame stored)

open Lean Elab Command Meta in
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
run_cmd do
  let mut previous : Option (Nat × Nat) := none
  let mut excessive := false
  for width in ([16, 64, 256] : List Nat) do
    let start ← IO.getNumHeartbeats
    let (claim, proof) ← liftTermElabM do
      let claim ← Term.elabType (← `(Stepped $(quote width)))
      let proof ← Term.elabTermAndSynthesize (← `(by
        unfold Stepped
        dsimp only
        constructor <;> cil_checked_step [])) (some claim)
      return (← instantiateMVars claim, ← instantiateMVars proof)
    let elaborated ← IO.getNumHeartbeats
    match Kernel.check (← getEnv) {} (Expr.letE `checked claim proof (.bvar 0) false) with
    | .error error => throwKernelException error
    | .ok _ => pure ()
    let frontend := elaborated - start
    let kernel := (← IO.getNumHeartbeats) - elaborated
    logInfo m!"initialized aggregate, {width} bytes: {frontend} frontend, {kernel} kernel"
    -- Quadrupling the width allows up to 25% more work per byte.
    if let some (lastFrontend, lastKernel) := previous then
      excessive := excessive || frontend > 5 * lastFrontend || kernel > 5 * lastKernel
    previous := some (frontend, kernel)
  if excessive then throwError "aggregate store/readback work per byte grew by more than 25%"

/-- A compiled read of every stored byte, including the untouched cell before the store. -/
@[noinline] private def sumCells (stored : Memory) (width : Nat) : Nat := Id.run do
  let mut sum := (stored.cells 0 0).bits.toNat
  for offset in [:width] do
    sum := sum + (stored.cells 0 (offset + 1)).bits.toNat
  return sum

/-- Nanoseconds per compiled cell read over repeated sweeps of one checked store. -/
private def nanosPerCell (width : Nat) : IO Nat := do
  let bytes := payload width
  let .ok stored := write (memory width) ⟨0, 1⟩ bytes 1
    | throw (IO.userError "aggregate write failed")
  let expected := bytes.foldl (fun sum bits => sum + bits.toNat) 0
  let start ← IO.monoNanosNow
  let mut sweeps := 0
  let mut total := 0
  repeat
    total := total + sumCells stored width
    sweeps := sweeps + 1
    let elapsed := (← IO.monoNanosNow) - start
    if elapsed >= 20_000_000 then
      unless total == sweeps * expected do throw (IO.userError "aggregate readback failed")
      return elapsed / (width * sweeps)

/-- Two of three paired measurements must stay within twice the small store's cost per byte. -/
private def checkCompiledCost : IO Unit := do
  let mut slow := 0
  for _ in [:3] do
    let small ← nanosPerCell 16
    let large ← nanosPerCell 4096
    IO.println s!"compiled aggregate, 16 and 4096 bytes: {small} and {large} ns/cell"
    if large > 2 * small then slow := slow + 1
  if slow >= 2 then
    throw (IO.userError "compiled aggregate reads exceeded twice the 16-byte cost per cell")

#eval checkCompiledCost

end WriteReadback

end Tests.AggregateMemorySteps
