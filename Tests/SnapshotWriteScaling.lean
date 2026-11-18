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

/-- Consecutive byte values with alternating initialization flags expose reordered cells. -/
private def payload (width : Nat) (seed : Nat := 0) : List (Prod (BitVec 8) Bool) :=
  (List.range width).map fun index => (BitVec.ofNat 8 (index + seed), index % 2 == 0)

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

/-- Both instructions operate on the same stack address and execution frame. -/
private def Stepped (width : Nat) : Prop :=
  let body : CIL.Method := { code := [], locals := [], returnsValue := false }
  let frame : Frame := Frame.mk 0 [] [] 0
  let address := Value.reference (.address target)
  let value := Value.scalar (.snapshot (.aggregate width) (payload width))
  let stored := (writeSnapshot (memory width) target (payload width) 1).toOption.getD Memory.empty
  And
    (step body (.storeAggregate width) 0 [] frame [value, address] (memory width) =
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

end Tests.SnapshotWriteScaling
