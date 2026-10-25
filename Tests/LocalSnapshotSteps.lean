import CIL.Safety.LocalSnapshotSteps

/-!
# Snapshot-aware checked execution tests

Numeric stores and loads compose through one snapshot fact, with abstract local homes and
caller memory. Missing authority remains a proof obligation.
-/

namespace Tests.LocalSnapshotSteps

open CIL.Safety

/-- Store both inputs, read the vector, and return the stored int32. -/
@[cil_code] def storeBoth : CIL.Method := {
  code := [.arg 0, .setLocal 0, .arg 1, .setLocal 1, .local 0, .pop, .local 1, .ret]
  locals := [.v128 0, .i32 0], returnsValue := true }

/-- A single empty snapshot collection follows stores and reloads through the whole body. -/
theorem store_and_reload {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {vectorHome intHome : Reference}
    (homes : WritableHomes entered boundary [.vector128, .word32] frame.locals)
    (formed : memory.WellFormed)
    (vectorSlot : frame.locals[0]? = some (.bytes .vector128 vectorHome))
    (intSlot : frame.locals[1]? = some (.bytes .word32 intHome))
    (vectorReady : access memory vectorHome 16 1 true = .ok ())
    (intReady : access memory intHome 4 1 true = .ok ())
    (vector : BitVec 128) (count : BitVec 32) :
    ∃ after, run [storeBoth] 9 0 0 [.scalar (.v128 vector), .scalar (.i32 count)]
      frame [] memory = .ok (after, [.scalar (.i32 count)]) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  cil_checked_steps (snapshots := snapshots) [vectorSlot, intSlot, vectorReady, intReady]

#print axioms store_and_reload

/-- Overwrite the vector after the int32 store, then reload both locals. -/
@[cil_code] def overwriteVector : CIL.Method := {
  code := [.arg 0, .setLocal 0, .arg 1, .setLocal 1, .arg 2, .setLocal 0,
    .local 1, .pop, .local 0, .ret]
  locals := [.v128 0, .i32 0], returnsValue := true }

/-- A later store replaces the remembered vector while preserving the int32 snapshot. -/
theorem overwrite_and_reload {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {vectorHome intHome : Reference}
    (homes : WritableHomes entered boundary [.vector128, .word32] frame.locals)
    (formed : memory.WellFormed)
    (vectorSlot : frame.locals[0]? = some (.bytes .vector128 vectorHome))
    (intSlot : frame.locals[1]? = some (.bytes .word32 intHome))
    (vectorReady : access memory vectorHome 16 1 true = .ok ())
    (intReady : access memory intHome 4 1 true = .ok ())
    (first last : BitVec 128) (count : BitVec 32) :
    ∃ after, run [overwriteVector] 11 0 0
      [.scalar (.v128 first), .scalar (.i32 count), .scalar (.v128 last)] frame [] memory =
        .ok (after, [.scalar (.v128 last)]) := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  cil_checked_steps (snapshots := snapshots) [vectorSlot, intSlot, vectorReady, intReady]

#print axioms overwrite_and_reload

/-- A snapshot collection grants no authority to write a local. -/
theorem missing_authority {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {vectorHome : Reference}
    (_homes : WritableHomes entered boundary [.vector128, .word32] frame.locals)
    (_formed : memory.WellFormed)
    (_slot : frame.locals[0]? = some (.bytes .vector128 vectorHome))
    (_vector : BitVec 128) : True := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  fail_if_success
    have : ∃ after,
      run [storeBoth] 8 0 1 [] frame [.scalar (.v128 _vector)] memory = .ok (after, []) := by
      cil_checked_steps (snapshots := snapshots) []
  trivial

#print axioms missing_authority

/-- Write authority cannot justify storing an int32 into a vector home. -/
theorem wrong_local_kind {entered memory : Memory} {frame : Frame} {boundary : Nat}
    {vectorHome : Reference}
    (_homes : WritableHomes entered boundary [.vector128, .word32] frame.locals)
    (_formed : memory.WellFormed)
    (_slot : frame.locals[0]? = some (.bytes .vector128 vectorHome))
    (_ready : access memory vectorHome 16 1 true = .ok ()) : True := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  fail_if_success
    have : ∃ after,
        run [storeBoth] 8 0 1 [] frame [.scalar (.i32 42)] memory = .ok (after, []) := by
      cil_checked_steps (snapshots := snapshots) []
  trivial

#print axioms wrong_local_kind

/-- An empty collection cannot turn an uninitialized load into a known value. -/
theorem unknown_load (memory : Memory) (frame : Frame) : True := by
  have snapshots := LocalSnapshots.empty memory frame.locals
  fail_if_success
    have : ∃ after,
      run [storeBoth] 5 0 4 [] frame [] memory = .ok (after, [.scalar (.i32 0)]) := by
      cil_checked_steps (snapshots := snapshots) []
  trivial

#print axioms unknown_load

end Tests.LocalSnapshotSteps
