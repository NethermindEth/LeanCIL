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

-- New value-only instructions must reject invalid operands in the checked dispatcher.
private def scalarBody : CIL.Method := { code := [], locals := [], returnsValue := true }
private def scalarFrame : Frame := { activation := 0, locals := [], owned := [] }

theorem nop_preserves_stack (stack : List Value) (memory : Memory) :
    step scalarBody .nop 7 [] scalarFrame stack memory =
      .ok (.next 8 stack scalarFrame memory) := rfl

theorem neg_underflow :
    (step scalarBody .neg 0 [] scalarFrame [] Examples.empty).isOk = false := rfl

theorem neg_reference_rejected :
    (step scalarBody .neg 0 [] scalarFrame [Examples.reference] Examples.caller).isOk = false := rfl

theorem gt_mixed_width_rejected :
    (step scalarBody .gt 0 [] scalarFrame [.scalar (.i32 0), .scalar (.i64 0)] Examples.empty).isOk = false := rfl

theorem branches_reject_underflow :
    ([CIL.Op.bgt 1, .ble 1, .bleu 1].all fun op =>
      !(step scalarBody op 0 [] scalarFrame [.scalar (.i32 0)] Examples.empty).isOk) = true := rfl

theorem branches_reject_references :
    ([CIL.Op.bgt 1, .ble 1, .bleu 1].all fun op =>
      !(step scalarBody op 0 [] scalarFrame [Examples.reference, Examples.reference] Examples.caller).isOk) = true := rfl

theorem branches_reject_mixed_widths :
    ([CIL.Op.bgt 1, .ble 1, .bleu 1].all fun op =>
      !(step scalarBody op 0 [] scalarFrame [.scalar (.i32 0), .scalar (.i64 0)] Examples.empty).isOk) = true := rfl

theorem narrow_conversions_reject_references :
    ([CIL.Op.convI1, .convI2, .convU2].all fun op =>
      !(step scalarBody op 0 [] scalarFrame [Examples.reference] Examples.caller).isOk) = true := rfl

theorem narrow_read_bounds :
    loadValue Examples.caller (.address ⟨0, 7⟩) 2 true =
      .error (.memory .outsideAllocation (.address ⟨0, 7⟩) 2) := rfl

theorem scalar_load_rejects_snapshot :
    (instruction (.loadScalar 2) [.scalar (.aggregate [1, 2])] Examples.caller).isOk = false := rfl

theorem scalar_width_rejected :
    instruction (.loadScalar 16) [Examples.reference] Examples.caller =
      .error (.unsupported "Scalar memory width") := rfl

theorem scalar_load_null :
    instruction (.loadScalar 4) [.reference .null] Examples.caller =
      .error (.memory .nullDereference .null 4) := rfl

theorem scalar_store_null :
    instruction (.storeScalar 4) [.scalar (.i32 7), .reference .null] Examples.caller =
      .error (.memory .nullDereference .null 0) := rfl

theorem scalar_store_wrong_width :
    instruction (.storeScalar 2) [.scalar (.i64 7), Examples.reference] Examples.caller =
      .error .invalidState := rfl

theorem scalar_store_bounds :
    instruction (.storeScalar 4) [.scalar (.i32 7), .reference (.address ⟨0, 6⟩)] Examples.caller =
      .error (.memory .outsideAllocation (.address ⟨0, 6⟩) 4) := rfl

theorem scalar_store_lifetime :
    instruction (.storeScalar 2) [.scalar (.i32 7), Examples.reference] (expire Examples.caller 0) =
      .error (.memory .expiredLifetime (.address ⟨0, 0⟩) 2) := rfl

theorem scalar_store_load {memory : Memory} {reference : Reference} (bits : CIL.W32)
    (ready : access memory reference 4 1 true = .ok ()) :
    ∃ result,
      instruction (.storeScalar 4) [.scalar (.i32 bits), .reference (.address reference)] memory =
        .ok (result, []) ∧
      instruction (.loadScalar 4) [.reference (.address reference)] result =
        .ok (result, [.scalar (.i32 bits)]) := by
  obtain ⟨result, stored, loaded⟩ := store_load_numeric_local .word32 (.i32 bits) bits.toNat rfl ready
  refine ⟨result, ?_, ?_⟩
  · cases hw : checkedAt (.address reference) 4 (write memory reference (numberBytes bits.toNat 4) 1) <;>
      simp_all [instruction, storeLocal, localNumber, referenceAt, localWidth, ordinaryAccessAlignment,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  · cases hr : checkedAt (.address reference) 4 (read result reference 4 1) <;>
      simp_all [instruction, loadLocal, loadValue, localWidth, localResult, dereference, ordinaryAccessAlignment,
        Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem switch_unsigned_default :
    step scalarBody (.switch [10, 20]) 3 [] scalarFrame [.scalar (.i32 4294967295)] Examples.empty =
      .ok (.next 4 [] scalarFrame Examples.empty) := rfl

theorem switch_rejects_non_i32 :
    (step scalarBody (.switch [10]) 0 [] scalarFrame [.scalar (.i64 0)] Examples.empty).isOk = false := rfl

theorem narrow_read_lifetime :
    loadValue (expire Examples.caller 0) (.address ⟨0, 0⟩) 2 true =
      .error (.memory .expiredLifetime (.address ⟨0, 0⟩) 2) := rfl

theorem narrow_write_permission :
    instruction (.setFieldAt 0 2) [.scalar (.i32 65535), Examples.reference]
      { Examples.caller with views := [⟨0, 0, 8, true, false⟩] } =
        .error (.memory .unwritable (.address ⟨0, 0⟩) 2) := rfl

theorem narrow_local_roundtrip {memory : Memory} {reference : Reference}
    (kind : CIL.NarrowKind) (bits : CIL.W32)
    (ready : access memory reference kind.width 1 true = .ok ()) :
    ∃ result,
      storeLocal memory (.bytes (.narrow kind) reference) (.scalar (.i32 bits)) =
        .ok (.bytes (.narrow kind) reference, result) ∧
      loadLocal result (.bytes (.narrow kind) reference) = .ok (.scalar (.i32 (kind.extend bits))) := by
  exact store_load_numeric_local (.narrow kind) (.i32 bits) bits.toNat rfl ready

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

namespace Tests

theorem division_mixed_widths_rejected :
    CIL.divideValues false false (.i32 6) (.i64 2) = .error .invalidOperands := rfl

theorem division_reference_rejected :
    CIL.divideValues true false .nullRef (.i32 2) = .error .invalidOperands := rfl

theorem division_zero (signed remainder : Bool) (x : CIL.W64) :
    CIL.divideBits signed remainder x 0 = .error .divideByZero := by
  simp [CIL.divideBits]

theorem division_underflow :
    (CIL.Safety.step { returnsValue := true, locals := [], code := [] }
      (.divide false false) 0 [] ⟨0, [], [], []⟩ [] Examples.empty).isOk = false := rfl

theorem division_managed_reference_rejected :
    (CIL.Safety.step { returnsValue := true, locals := [], code := [] }
      (.divide false false) 0 [] ⟨0, [], [], []⟩
      [.scalar (.i32 2), .reference .null] Examples.empty).isOk = false := rfl

end Tests
