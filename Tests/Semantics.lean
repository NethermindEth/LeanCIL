import Examples.Support
import CIL.Safety.ExecutionInvariants
import CIL.Safety.NumericLocalLoad

open CIL.Safety
namespace Tests

theorem vector_lane_add :
    CIL.evalIntrinsic (.vector (.add64 128))
      [.v128 (CIL.Vector.pack128 1 2), .v128 (CIL.Vector.pack128 3 4)] =
      some (.v128 (CIL.Vector.pack128 4 6)) := rfl

theorem disabled_intrinsic :
    (CIL.step (.intrinsic (.avx2 .add64) 2) false 0 [] 0
      [.v256 1, .v256 2] (fun _ => none)).isSome = false := rfl

theorem integer_wrap : CIL.binary .add (.i32 4294967295) (.i32 1) = some (.i32 0) := rfl

theorem uninitialized_rejected :
    read { Examples.caller with cells := fun _ _ => ⟨0, false⟩ } ⟨0, 0⟩ 8 1 = .error .uninitialized := rfl

theorem expired_rejected : read (expire Examples.caller 0) ⟨0, 0⟩ 8 1 = .error .expiredLifetime := rfl

theorem sentinel_forms : form Examples.caller ⟨0, 8⟩ = .ok ⟨0, 8⟩ := rfl

theorem sentinel_cannot_read : read Examples.caller ⟨0, 8⟩ 1 1 = .error .outsideAllocation := rfl

theorem no_write_permission :
    write { Examples.caller with views := [⟨0, 0, 8, true, false⟩] } ⟨0, 0⟩ [1] 1 = .error .unwritable := rfl

theorem null_rejected : dereference Examples.caller .null 8 1 = .error .nullDereference := rfl

theorem malformed_allocation :
    (allocate Examples.empty ⟨.callerStack, ⟨8, 0, []⟩, true, []⟩).isOk = false := rfl

theorem gc_slot_rejected :
    read { Examples.caller with allocations := fun _ => some ⟨.managedHeap, ⟨8, 1, [(0, 8)]⟩, true, []⟩ }
      ⟨0, 0⟩ 8 1 = .error .unsupportedLayout := rfl

theorem unknown_instruction_rejected :
    (instruction (.unsupported "test") [] Examples.empty).isOk = false := rfl

-- Generic round-trip theorem now covers arbitrary bounded aggregate lengths.
theorem aggregate_roundtrip {memory : Memory} {reference : Reference}
    (size : Fin (2^64)) (bytes : List (BitVec 8)) (length : bytes.length = size.val)
    (ready : access memory reference size.val 1 true = .ok ()) :
    ∃ result,
      storeLocal memory (.bytes (.aggregate size) reference) (.scalar (.aggregate bytes)) =
        .ok (.bytes (.aggregate size) reference, result) ∧
      loadLocal result (.bytes (.aggregate size) reference) = .ok (.scalar (.aggregate bytes)) := by
  apply store_load_numeric_local (.aggregate size) (.aggregate bytes) (byteNumber bytes)
  · simp [localNumber, length]
  · exact ready

#print axioms aggregate_roundtrip
end Tests
