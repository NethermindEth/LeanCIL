import Tests.AggregateSetup
import Tests.ValueBitCasts
import Tests.ViewReuse
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

theorem unsigned_compare_wraps :
    CIL.binary .ltu (.i64 (BitVec.ofNat 64 (2^64-1))) (.i64 0) = some (.i32 0) := by decide

theorem add_wraps_at_width :
    CIL.binary .add (.i64 (BitVec.ofNat 64 (2^64-1))) (.i64 1) = some (.i64 0) := by decide

theorem write_overwrites (m : CIL.Memory) (a : CIL.Address) (x y : CIL.Value) :
    CIL.write (CIL.write m a x) a y a = some y := by simp [CIL.write]

-- New value-only instructions must reject invalid operands in the checked dispatcher.
private def scalarBody : CIL.Method := { code := [], locals := [], returnsValue := true }
private def scalarFrame : Frame := { activation := 0, locals := [], owned := [] }

theorem checked_disabled_intrinsic (body : CIL.Method) (operation : CIL.Intrinsic)
    (disabled : operation.available body.profile = false) (argc pc : Nat)
    (args stack : List Value) (frame : Frame) (memory : Memory) :
    step body (.intrinsic operation argc) pc args frame stack memory =
      .error (.unsupported "Intrinsic unavailable in target profile") := by
  simp [step, disabled, observerCount, unspecifiedOperands]

theorem checked_avx2_enabled :
    step { scalarBody with profile := { avx2 := true } } (.intrinsic (.avx2 .add64) 2)
      0 [] scalarFrame [.scalar (.v256 1), .scalar (.v256 2)] Examples.empty =
      .ok (.next 1 [.scalar (.v256 3)] scalarFrame Examples.empty) := rfl

theorem checked_avx512_disabled :
    step scalarBody (.intrinsic (.avx512 .ltu64) 2) 0 [] scalarFrame
      [.scalar (.v256 1), .scalar (.v256 2)] Examples.empty =
      .error (.unsupported "Intrinsic unavailable in target profile") := rfl

theorem checked_avx512_invocation_disabled (memory : Memory) :
    invoke [{ code := [.arg 0, .arg 1, .intrinsic (.avx512 .ltu64) 2, .ret], locals := [], returnsValue := true }] 4 0
      [.scalar (.v256 1), .scalar (.v256 2)] memory =
      .error ⟨0, 2, .unsupported "Intrinsic unavailable in target profile"⟩ := rfl

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
  change (do
    let bytes ← checkedAt (.address reference) 4 (read result reference 4 1)
    pure (Value.scalar (.i32 (BitVec.ofNat 32 (byteNumber bytes)))) : ExecutionResult Value) = _ at loaded
  refine ⟨result, ?_, ?_⟩
  · cases hw : checkedAt (.address reference) 4 (write memory reference (numberBytes bits.toNat 4) 1) <;>
      simp_all [instruction, storeLocal, localNumber, referenceAt, localWidth, ordinaryAccessAlignment,
        observerCount, unspecifiedOperands, Value.hasUnspecified, CIL.Value.hasUnspecified,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
  · cases hr : checkedAt (.address reference) 4 (read result reference 4 1) <;>
      simp_all [instruction, loadValue, localResult, dereference, ordinaryAccessAlignment,
        observerCount, unspecifiedOperands, Value.hasUnspecified, CIL.Value.hasUnspecified,
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
  · simp [localNumber, length, CIL.Value.hasUnspecified]
  · exact ready

#print axioms aggregate_roundtrip
theorem missing_parameter_rejected :
    CIL.Safety.makeParameterHomes 0 [(0, .word32)] [] Examples.empty = .error .invalidState := rfl

theorem reference_parameter_rejects_integer :
    CIL.Safety.makeParameterHomes 0 [(0, .reference)] [.scalar (.i32 0)] Examples.empty =
      .error .invalidState := rfl

theorem scalar_parameter_rejects_reference :
    (CIL.Safety.makeParameterHomes 0 [(0, .word32)] [.reference .null] Examples.empty).isOk = false := rfl

theorem parameter_initialization_narrows :
    (do
      let (homes, _, memory) ← CIL.Safety.makeParameterHomes 0 [(0, .narrow .signed8)]
        [.scalar (.i32 255)] Examples.empty
      let some (_, slot) := homes[0]? | .error .invalidState
      CIL.Safety.loadLocal memory slot : CIL.Safety.ExecutionResult CIL.Safety.Value) =
      .ok (.scalar (.i32 4294967295)) := rfl

-- Typed copies share scalar memory permissions, lifetime and initialization checks.
def copyMemory : Memory := {
  Examples.empty with
  allocations := fun id => if id < 2 then some ⟨.callerStack, ⟨12, 1, []⟩, true, [12]⟩ else none
  cells := fun _ _ => ⟨42, true⟩
  views := [⟨0, 0, 12, true, true⟩, ⟨1, 0, 12, true, true⟩]
  nextIdentity := 2
}

def copyStack : List Value := [.reference (.address ⟨0, 0⟩), .reference (.address ⟨1, 0⟩)]

theorem copy_uninitialized :
    (instruction (.copyObject 8) copyStack { copyMemory with cells := fun _ _ => ⟨0, false⟩ }).map Prod.snd =
      .error (.memory .uninitialized (.address ⟨0, 0⟩) 8) := rfl

theorem copy_unreadable :
    (instruction (.copyObject 8) copyStack { copyMemory with views := [⟨1, 0, 12, true, true⟩] }).map Prod.snd =
      .error (.memory .unreadable (.address ⟨0, 0⟩) 8) := rfl

theorem copy_unwritable :
    (instruction (.copyObject 8) copyStack { copyMemory with views := [⟨0, 0, 12, true, true⟩] }).map Prod.snd =
      .error (.memory .unwritable (.address ⟨1, 0⟩) 8) := rfl

theorem copy_expired :
    (instruction (.copyObject 8) copyStack { copyMemory with
      allocations := fun _ => some ⟨.callerStack, ⟨12, 1, []⟩, false, []⟩ }).map Prod.snd =
      .error (.memory .expiredLifetime (.address ⟨0, 0⟩) 8) := rfl

theorem copy_gc_slot :
    (instruction (.copyObject 8) copyStack { copyMemory with
      allocations := fun _ => some ⟨.callerStack, ⟨12, 1, [(0, 8)]⟩, true, []⟩ }).map Prod.snd =
      .error (.memory .unsupportedLayout (.address ⟨0, 0⟩) 8) := rfl

theorem copy_source_bounds :
    (instruction (.copyObject 8) [.reference (.address ⟨0, 12⟩), .reference (.address ⟨1, 0⟩)] copyMemory).map Prod.snd =
      .error (.memory .outsideAllocation (.address ⟨0, 12⟩) 8) := rfl

theorem copy_destination_bounds :
    (instruction (.copyObject 8) [.reference (.address ⟨0, 0⟩), .reference (.address ⟨1, 12⟩)] copyMemory).map Prod.snd =
      .error (.memory .outsideAllocation (.address ⟨1, 12⟩) 8) := rfl

theorem copy_null_source :
    (instruction (.copyObject 8) [.reference .null, .reference (.address ⟨1, 0⟩)] copyMemory).map Prod.snd =
      .error (.memory .nullDereference .null 0) := rfl

theorem copy_null_destination :
    (instruction (.copyObject 8) [.reference (.address ⟨0, 0⟩), .reference .null] copyMemory).map Prod.snd =
      .error (.memory .nullDereference .null 0) := rfl

theorem copy_partial_overlap :
    (instruction (.copyObject 8) [.reference (.address ⟨0, 0⟩), .reference (.address ⟨0, 4⟩)] copyMemory).map Prod.snd =
      .error (.unsupported "Partially overlapping typed copy") := rfl

theorem scalar_helper_wrong_width :
    CIL.evalScalarIntrinsic (.rotateLeft 64) [.i32 1, .i32 2] = none := rfl

theorem scalar_helper_wrong_arity :
    CIL.evalScalarIntrinsic (.popCount 64) [.i64 1, .i64 2] = none := rfl

theorem scalar_helper_wrong_type :
    CIL.evalScalarIntrinsic (.reverseEndianness 32 false) [.nullRef] = none := rfl

theorem scalar_helper_unsupported_width :
    CIL.evalScalarIntrinsic (.reverseEndianness 24 false) [.i32 1] = none := rfl

theorem scalar_helper_zero_counts :
    CIL.evalScalarIntrinsic (.leadingZeroCount 64) [.i64 0] = some (.i32 64) ∧
    CIL.evalScalarIntrinsic (.trailingZeroCount 32) [.i32 0] = some (.i32 32) := ⟨rfl, rfl⟩

theorem nested_snapshot_bounds :
    (instruction (.aggregateFieldAt 3 2) [.scalar (.aggregate [1, 2, 3, 4])] Examples.empty).map Prod.snd =
      .error .invalidState := rfl

theorem nested_store_size :
    (instruction (.setAggregateFieldAt 0 8) [.scalar (.aggregate [1]), Examples.reference] Examples.caller).map Prod.snd =
      .error .invalidState := rfl

theorem nested_null :
    (instruction (.aggregateFieldAt 0 8) [.reference .null] Examples.empty).map Prod.snd =
      .error (.memory .nullDereference .null 0) := rfl

theorem null_reference_pushed :
    instruction (.memory .nullRef) [.scalar (.i32 7)] Examples.empty =
      .ok (Examples.empty, [.reference .null, .scalar (.i32 7)]) := rfl

theorem null_reference_detected :
    instruction (.memory .isNullRef) [.reference .null] Examples.empty =
      .ok (Examples.empty, [.scalar (.i32 1)]) := rfl

theorem live_reference_not_null :
    instruction (.memory .isNullRef) [Examples.reference] Examples.caller =
      .ok (Examples.caller, [.scalar (.i32 0)]) := rfl

-- Testing performs no access, so an expired reference is still not null.
theorem expired_reference_not_null :
    instruction (.memory .isNullRef) [Examples.reference] (expire Examples.caller 0) =
      .ok (expire Examples.caller 0, [.scalar (.i32 0)]) := rfl

theorem null_test_requires_reference :
    instruction (.memory .isNullRef) [.scalar (.i64 0)] Examples.empty = .error .invalidState := rfl

-- Every load and store through `NullRef` faults as a null dereference.
theorem null_reference_accesses_fault :
    instructions [.memory .nullRef, .load64] [] Examples.empty =
      .error (.memory .nullDereference .null 8) ∧
    instructions [.memory .nullRef, .loadScalar 4 true] [] Examples.empty =
      .error (.memory .nullDereference .null 4) ∧
    instructions [.memory .nullRef, .const64 7, .store64] [] Examples.empty =
      .error (.memory .nullDereference .null 0) ∧
    instructions [.memory .nullRef, .const32 7, .storeScalar 4] [] Examples.empty =
      .error (.memory .nullDereference .null 0) ∧
    instructions [.memory .nullRef, .loadAggregate 32] [] Examples.empty =
      .error (.memory .nullDereference .null 32) ∧
    instructions [.memory .nullRef, .initAggregate 32] [] Examples.empty =
      .error (.memory .nullDereference .null 0) ∧
    instructions [.memory .nullRef, .memory .load256] [] Examples.empty =
      .error (.memory .nullDereference .null 32) ∧
    instructions [.memory .nullRef, .fieldAt 8 8] [] Examples.empty =
      .error (.memory .nullDereference .null 0) ∧
    instructions [.memory .nullRef, .fieldAddress 8] [] Examples.empty =
      .error (.memory .nullDereference .null 0) ∧
    instructions [.memory .nullRef, .const64 7, .setFieldAt 8 8] [] Examples.empty =
      .error (.memory .nullDereference .null 0) ∧
    instructions [.memory .nullRef, .lane 1] [] Examples.empty =
      .error (.memory .nullDereference .null 0) ∧
    instructions [.memory .nullRef, .laneAddress 1] [] Examples.empty =
      .error (.memory .nullDereference .null 0) ∧
    instructions [.memory .nullRef, .const64 7, .setLane 1] [] Examples.empty =
      .error (.memory .nullDereference .null 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nested_uninitialized :
    (instruction (.aggregateFieldAt 0 8) [Examples.reference]
      { Examples.caller with cells := fun _ _ => ⟨0, false⟩ }).map Prod.snd =
      .error (.memory .uninitialized (.address ⟨0, 0⟩) 8) := rfl

theorem nested_bounds :
    (instruction (.aggregateFieldAt 4 8) [Examples.reference] Examples.caller).map Prod.snd =
      .error (.memory .outsideAllocation (.address ⟨0, 4⟩) 8) := rfl

theorem nested_unwritable :
    (instruction (.setAggregateFieldAt 0 8) [.scalar (.aggregate (List.replicate 8 0)), Examples.reference]
      { Examples.caller with views := [⟨0, 0, 8, true, false⟩] }).map Prod.snd =
      .error (.memory .unwritable (.address ⟨0, 0⟩) 8) := rfl

theorem nested_expired :
    (instruction (.aggregateFieldAt 0 8) [Examples.reference] { Examples.caller with
      allocations := fun _ => some ⟨.callerStack, ⟨8, 1, []⟩, false, []⟩ }).map Prod.snd =
      .error (.memory .expiredLifetime (.address ⟨0, 0⟩) 0) := rfl

theorem constructor_zero_size :
    step { returnsValue := true, locals := [], code := [] } (.newAggregate 1 0 0)
      0 [] ⟨0, [], [], []⟩ [] Examples.empty = .error .invalidState := rfl

theorem constructor_stack_underflow :
    step { returnsValue := true, locals := [], code := [] } (.newAggregate 1 1 3)
      0 [] ⟨0, [], [], []⟩ [] Examples.empty = .error .invalidState := rfl

def constructorCaller : CIL.Method := {
  returnsValue := true, locals := [], code := [.newAggregate 1 0 3, .ret] }

theorem constructor_zero_initialization :
    (invoke [constructorCaller, { returnsValue := false, locals := [], code := [.ret] }]
      8 0 [] Examples.empty).map Prod.snd = .ok [.scalar (.aggregate [0, 0, 0])] := rfl

theorem constructor_must_return_void :
    (invoke [constructorCaller, { returnsValue := true, locals := [], code := [.const32 7, .ret] }]
      8 0 [] Examples.empty).map Prod.snd = .error ⟨0, 0, .invalidState⟩ := rfl

end Tests

namespace Tests

theorem division_mixed_widths_rejected :
    CIL.divideValues false false (.i32 6) (.i64 2) = .error .invalidOperands := rfl

theorem checked_mixed_widths_rejected :
    CIL.checkedValues .add false (.i32 6) (.i64 2) = .error .invalidOperands := rfl

theorem checked_conversion_bad_width :
    CIL.convertInteger 7 false true (.i32 1) = .error .invalidOperands := rfl

theorem native_memory_dispatch_rejected :
    CIL.nativeBinaryValues .load64 0 (.i64 0) (.i32 0) = .error .invalidOperands := rfl

theorem native_nested_dispatch_rejected :
    CIL.nativeBinaryValues (.nativeBinary .add) 0 (.i64 0) (.i32 0) = .error .invalidOperands := rfl

theorem native_reference_operand_rejected :
    CIL.nativeBinaryValues .add 0 .nullRef (.i32 0) = .error .invalidOperands := rfl

theorem native_mixed_signed_extension :
    CIL.nativeBinaryValues .add 0 (.i64 1) (.i32 4294967295) = .ok (1, [.i64 0]) := rfl

theorem native_checked_unsigned_extension :
    CIL.nativeBinaryValues (.checkedArithmetic .add false) 0 (.i64 1) (.i32 4294967295) =
      .ok (1, [.i64 4294967296]) := rfl

theorem native_unsigned_branch_rejected :
    CIL.nativeBinaryValues (.bne 9) 0 (.i64 18446744073709551615) (.i32 4294967295) =
      .error .invalidOperands := rfl

theorem native_unsigned_branch_family_rejected :
    CIL.nativeBinaryValues (.bltu 9) 0 (.i64 0) (.i32 4294967295) = .error .invalidOperands ∧
    CIL.nativeBinaryValues (.bgtu 9) 0 (.i64 0) (.i32 4294967295) = .error .invalidOperands ∧
    CIL.nativeBinaryValues (.bleu 9) 0 (.i64 0) (.i32 4294967295) = .error .invalidOperands ∧
    CIL.nativeBinaryValues (.bgeu 9) 0 (.i64 0) (.i32 4294967295) = .error .invalidOperands :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem native_unsigned_compare_extension :
    CIL.nativeBinaryValues .gtu 0 (.i64 18446744073709551615) (.i32 4294967295) =
      .ok (1, [.i32 0]) := rfl

theorem checked_conversion_reference_rejected :
    CIL.convertInteger 32 false true .nullRef = .error .invalidOperands := rfl

theorem checked_conversion_sign_extension :
    CIL.convertInteger 8 true false (.i64 18446744073709551615) = .ok (.i32 4294967295) := rfl

theorem checked_conversion_unsigned_input_overflow :
    CIL.convertInteger 8 true true (.i32 4294967295) = .error .overflow := rfl

theorem checked_reference_rejected :
    CIL.checkedValues .mul true .nullRef (.i32 2) = .error .invalidOperands := rfl

theorem checked_unsigned_subtraction_underflow :
    CIL.checkedValues .sub false (.i32 0) (.i32 1) = .error .overflow := rfl

theorem checked_signed_multiplication_overflow :
    CIL.checkedValues .mul true (.i64 9223372036854775808) (.i64 18446744073709551615) =
      .error .overflow := rfl

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


-- DivRem: (upper:lower) / divisor with Item1 = quotient, Item2 = remainder; upper ≥ divisor faults.
theorem divRem_boundary :
    CIL.X86.divRem64 (BitVec.ofNat 64 (2 ^ 64 - 1)) 2 3 = .ok (BitVec.ofNat 64 (2 ^ 64 - 1), 2) := rfl
theorem divRem_overflow : CIL.X86.divRem64 0 3 3 = .error .overflow := rfl
theorem divRem_zero : CIL.X86.divRem64 7 0 0 = .error .divideByZero := rfl
theorem divRem_operands : CIL.X86.divRemValue [.i64 1, .i32 0, .i64 3] = .error .invalidOperands := rfl

def divRemMethod (profile : CIL.FeatureProfile) : CIL.Method :=
  { profile, returnsValue := true, locals := [], code := [.intrinsic (.x86Base .divRem64) 3] }

theorem divRem_checked_fault :
    CIL.Safety.step (divRemMethod { architecture := .x64, x86Base64 := true }) (.intrinsic (.x86Base .divRem64) 3) 0 []
      ⟨0, [], [], []⟩ [.scalar (.i64 3), .scalar (.i64 3), .scalar (.i64 0)] Examples.empty =
      .error (.arithmetic .overflow) := rfl

theorem divRem_requires_x86Base :
    CIL.Safety.step (divRemMethod CIL.FeatureProfile.scalar) (.intrinsic (.x86Base .divRem64) 3) 0 []
      ⟨0, [], [], []⟩ [.scalar (.i64 3), .scalar (.i64 0), .scalar (.i64 7)] Examples.empty =
      .error (.unsupported "Intrinsic unavailable in target profile") := rfl

theorem divRem_pure_fault :
    CIL.evalIntrinsic (.x86Base .divRem64) [.i64 0, .i64 0, .i64 0] = none := rfl

end Tests
