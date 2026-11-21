import CIL.Safety.SymbolicExecution

/-! Standalone kernel, checked stepping and compiled workloads for snapshot write/readback. -/

namespace Tests.SnapshotWriteScaling

open CIL.Safety

/-- A writable allocation with room for one leading byte before the copied range. -/
private def memory (width : Nat) : Memory := { Memory.empty with
  allocations := fun id => if id == 0 then
    some (.mk .callerStack (.mk (width + 1) 1 []) true []) else none
  views := [.mk 0 0 (width + 1) true true]
  nextIdentity := 1 }

/-- The copy starts one byte into allocation zero. -/
private def target : Reference := { allocation := 0, offset := 1 }

/-- Each 256-byte block starts one value later. Initialization flags alternate. -/
private def payload (width : Nat) (seed : Nat := 0) : List (Prod (BitVec 8) Bool) :=
  (List.range width).map fun index =>
    (BitVec.ofNat 8 (index + index / 256 + seed), index % 2 == 0)

/-- Read back every byte and flag after the checked write. -/
private def roundTrip (width : Nat) (seed : Nat := 0) : Bool :=
  let bytes := payload width seed
  match writeSnapshot (memory width) target bytes 1 with
  | .ok stored =>
    match readSnapshot stored target width 1 with
    | .ok copied => copied == bytes
    | .error _ => false
  | .error _ => false

/-- Time 256 compiled copies, varying the payload on each iteration. -/
private def timeCopies (width : Nat) : IO Unit := do
  let start <- IO.monoNanosNow
  for seed in [:256] do
    unless roundTrip width seed do
      throw (IO.userError s!"readback failed at width {width}, seed {seed}")
  let elapsed := (<- IO.monoNanosNow) - start
  IO.println s!"{width} bytes, 256 copies, {elapsed} ns"

/-- Add one full sweep of the stored cell function to the running byte sum. -/
@[noinline] private def sumCells (stored : Memory) (width total : Nat) : Nat := Id.run do
  let mut sum := total
  for index in [:width] do
    sum := sum + (stored.cells target.allocation (target.offset + index)).bits.toNat
  return sum

/-- Measure complete sweeps of a successful store for at least 20 ms, in nanoseconds per byte. -/
private def nanosPerByte (width : Nat) : IO Nat := do
  let bytes := payload width
  let .ok stored := writeSnapshot (memory width) target bytes 1
    | throw (IO.userError s!"snapshot write failed at width {width}")
  let expected := bytes.foldl (fun sum cell => sum + cell.1.toNat) 0
  let mut sum := 0
  let mut sweeps := 0
  let start <- IO.monoNanosNow
  repeat
    for _ in [:1024 / width] do
      sum := sumCells stored width sum
      sweeps := sweeps + 1
    let elapsed := (<- IO.monoNanosNow) - start
    if elapsed >= 20_000_000 then
      unless sum == sweeps * expected do
        throw (IO.userError s!"cell sum failed at width {width}")
      let count := sweeps * width
      let cost := elapsed / count
      IO.println s!"{width}-byte store: {elapsed} ns / {count} cell reads = {cost} ns/byte"
      return cost

/-- At least two of three paired samples must stay within twice the small store's cost per byte. -/
private def checkCompiledCost : IO Unit := do
  let mut slow := 0
  for _ in [:3] do
    let small <- nanosPerByte 16
    let large <- nanosPerByte 1024
    if large > 2 * small then slow := slow + 1
  if slow >= 2 then
    throw (IO.userError s!"compiled cell reads exceeded 2x the 16-byte cost in {slow}/3 samples")

/-- Both instructions operate on the same stack address and execution frame. -/
private def Stepped (width : Nat) : Prop :=
  let type := CIL.Extraction.TypeExpr.aggregate "Fixture::Bytes" 0
  let raw : CIL.Extraction.RawLayout :=
    { identity := "Fixture::Bytes", explicit := true, packing := 1, declaredSize := width, fields := [] }
  let body : CIL.Method :=
    { code := [.stobj type], locals := [], returnsValue := false
      environment := { rawLayouts := [raw], layouts := #[⟨{ size := width, fields := [] }, 1⟩] } }
  let frame : Frame := Frame.mk 0 [] [] 0
  let address := Value.reference (.address target)
  let value := Value.scalar (.snapshot (.aggregate width) (payload width))
  let stored := (writeSnapshot (memory width) target (payload width) 1).toOption.getD Memory.empty
  And
    (step body (.stobj type) 0 [] frame [value, address] (memory width) =
      .ok (.next 1 [] frame stored))
    (step body (.loadAggregate width) 1 [] frame [address] stored =
      .ok (.next 2 [value] frame stored))

/-- The store and load each discharge a checked instruction goal. -/
local macro "check_copy" : tactic => `(tactic|
  (unfold Stepped
   dsimp only
   constructor <;> cil_checked_step []))

set_option maxRecDepth 65536
set_option maxHeartbeats 60000

/-- Kernel readback of 16 bytes. -/
theorem kernel16 : roundTrip 16 = true := by decide +kernel
#print axioms kernel16

/-- Checked store and load of a 16-byte aggregate. -/
theorem stepped16 : Stepped 16 := by check_copy
#print axioms stepped16

#eval timeCopies 16

/-- Kernel readback of 64 bytes. -/
theorem kernel64 : roundTrip 64 = true := by decide +kernel
#print axioms kernel64

/-- Checked store and load of a 64-byte aggregate. -/
theorem stepped64 : Stepped 64 := by check_copy
#print axioms stepped64

#eval timeCopies 64

/-- Kernel readback of 256 bytes stays within six million raw heartbeats. -/
theorem kernel256 : roundTrip 256 = true := by
  run_tac
    let started <- IO.getNumHeartbeats
    Lean.Elab.Tactic.evalTactic (<- `(tactic| decide +kernel))
    let cost := (<- IO.getNumHeartbeats) - started
    if cost > 6000000 then
      Lean.throwError m!"256-byte kernel readback used {cost} raw heartbeats"
#print axioms kernel256

/-- Checked store and load of a 256-byte aggregate. -/
theorem stepped256 : Stepped 256 := by check_copy
#print axioms stepped256

#eval timeCopies 256

#eval timeCopies 1024

#eval checkCompiledCost

end Tests.SnapshotWriteScaling
