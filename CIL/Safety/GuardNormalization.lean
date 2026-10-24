import CIL.Safety.Execution
import CIL.Safety.StepAttribute

/-!
# Guard normalization

Before dispatch, the checked `step` rejects an instruction whose observed operands carry
unspecified vector bits (`unspecifiedOperands (observerCount op) stack`). The `cil_guard`
simp set below evaluates that guard on concrete instructions and stack shapes, so stepping
tactics can discharge it to `false` without unfolding `observerCount`. The `localResult`
lemmas do the same for a value loaded from a local.
-/

namespace CIL.Safety

-- Only a 128-bit vector known in its low 64 bits has unspecified bits.
@[cil_guard] theorem guard_scalar (value : CIL.Value) :
    Value.hasUnspecified (.scalar value) = value.hasUnspecified := rfl
@[cil_guard] theorem guard_reference (value : ManagedReference) :
    Value.hasUnspecified (.reference value) = false := rfl
@[cil_guard] theorem guard_span (reference : ManagedReference) (length : Nat) :
    Value.hasUnspecified (.span reference length) = false := rfl

@[cil_guard] theorem guard_snapshot (shape : CIL.SnapshotShape) (bytes : List (BitVec 8 × Bool)) :
    CIL.Value.hasUnspecified (.snapshot shape bytes) = false := rfl
@[cil_guard] theorem guard_aggregate (bytes : List (BitVec 8)) :
    CIL.Value.hasUnspecified (.aggregate bytes) = false := rfl
@[cil_guard] theorem guard_i8 (value : BitVec 8) :
    CIL.Value.hasUnspecified (.i8 value) = false := rfl
@[cil_guard] theorem guard_i32 (value : CIL.W32) :
    CIL.Value.hasUnspecified (.i32 value) = false := rfl
@[cil_guard] theorem guard_i64 (value : CIL.W64) :
    CIL.Value.hasUnspecified (.i64 value) = false := rfl
@[cil_guard] theorem guard_v128 (value : BitVec 128) :
    CIL.Value.hasUnspecified (.v128 value) = false := rfl
@[cil_guard] theorem guard_v128Low64 (value : CIL.W64) :
    CIL.Value.hasUnspecified (.v128Low64 value) = true := rfl
@[cil_guard] theorem guard_v256 (value : BitVec 256) :
    CIL.Value.hasUnspecified (.v256 value) = false := rfl
@[cil_guard] theorem guard_v512 (value : BitVec 512) :
    CIL.Value.hasUnspecified (.v512 value) = false := rfl
@[cil_guard] theorem guard_scalar_span (address : CIL.Address) (length : Nat) :
    CIL.Value.hasUnspecified (.span address length) = false := rfl
@[cil_guard] theorem guard_object (id : Nat) :
    CIL.Value.hasUnspecified (.object id) = false := rfl
@[cil_guard] theorem guard_scalar_ref (address : CIL.Address) :
    CIL.Value.hasUnspecified (.ref address) = false := rfl
@[cil_guard] theorem guard_nullRef : CIL.Value.hasUnspecified .nullRef = false := rfl
@[cil_guard] theorem guard_unmodeled : CIL.Value.hasUnspecified .unmodeled = false := rfl

-- The guard inspects only the top `count` stack operands.
@[cil_guard] theorem guard_operands_zero (stack : List Value) :
    unspecifiedOperands 0 stack = false := rfl
@[cil_guard] theorem guard_operands_nil (count : Nat) :
    unspecifiedOperands count [] = false := by simp [unspecifiedOperands]
@[cil_guard] theorem guard_operands_cons (count : Nat) (value : Value) (rest : List Value) :
    unspecifiedOperands (Nat.succ count) (value :: rest) =
      (value.hasUnspecified || unspecifiedOperands count rest) := rfl

-- How many stack operands each instruction observes.
@[cil_guard] theorem guard_nativeBinary (op : CIL.Op) : observerCount (.nativeBinary op) = 2 := rfl
@[cil_guard] theorem guard_checkedConvert (width : Nat) (signed unsigned : Bool) :
    observerCount (.checkedConvert width signed unsigned) = 1 := rfl
@[cil_guard] theorem guard_checkedArithmetic (kind : CIL.CheckedBinaryKind) (signed : Bool) :
    observerCount (.checkedArithmetic kind signed) = 2 := rfl
@[cil_guard] theorem guard_divide (signed remainder : Bool) :
    observerCount (.divide signed remainder) = 2 := rfl
@[cil_guard] theorem guard_arg (index : Nat) (narrow : Option CIL.NarrowKind) :
    observerCount (.arg index narrow) = 0 := rfl
@[cil_guard] theorem guard_call (callee argc : Nat) :
    observerCount (.call callee argc) = argc := rfl
@[cil_guard] theorem guard_newVector256 (callee argc : Nat) :
    observerCount (.newVector256 callee argc) = argc := rfl
@[cil_guard] theorem guard_newAggregate (callee argc : Nat) (size : Fin (2^64)) :
    observerCount (.newAggregate callee argc size) = argc := rfl
@[cil_guard] theorem guard_memory (op : CIL.MemoryOp) :
    observerCount (.memory op) = op.argumentCount := rfl
@[cil_guard] theorem guard_throw (exception : String) : observerCount (.throw exception) = 0 := rfl
@[cil_guard] theorem guard_unsupported (description : String) :
    observerCount (.unsupported description) = 0 := rfl
@[cil_guard] theorem guard_ret : observerCount (.ret none) = 1 := rfl
@[cil_guard] theorem guard_ret_narrow (kind : CIL.NarrowKind) :
    observerCount (.ret (some kind)) = 1 := rfl
@[cil_guard] theorem guard_loadAggregate (size : Nat) :
    observerCount (.loadAggregate size) = 1 := rfl
@[cil_guard] theorem guard_storeAggregate (size : Nat) :
    observerCount (.storeAggregate size) = 2 := rfl
@[cil_guard] theorem guard_copyObject (size : Nat) : observerCount (.copyObject size) = 2 := rfl
@[cil_guard] theorem guard_initAggregate (size : Nat) :
    observerCount (.initAggregate size) = 1 := rfl
@[cil_guard] theorem guard_loadScalar (width : Nat) (signed : Bool) :
    observerCount (.loadScalar width signed) = 1 := rfl
@[cil_guard] theorem guard_storeScalar (width : Nat) : observerCount (.storeScalar width) = 2 := rfl
@[cil_guard] theorem guard_fieldAt (offset width : Nat) (signed : Bool) :
    observerCount (.fieldAt offset width signed) = 1 := rfl
@[cil_guard] theorem guard_fieldAddress (offset : Nat) :
    observerCount (.fieldAddress offset) = 1 := rfl
@[cil_guard] theorem guard_setFieldAt (offset width : Nat) :
    observerCount (.setFieldAt offset width) = 2 := rfl
@[cil_guard] theorem guard_aggregateFieldAt (offset size : Nat) :
    observerCount (.aggregateFieldAt offset size) = 1 := rfl
@[cil_guard] theorem guard_setAggregateFieldAt (offset size : Nat) :
    observerCount (.setAggregateFieldAt offset size) = 2 := rfl
@[cil_guard] theorem guard_lane (index : Fin 4) : observerCount (.lane index) = 1 := rfl
@[cil_guard] theorem guard_laneAddress (index : Fin 4) :
    observerCount (.laneAddress index) = 1 := rfl
@[cil_guard] theorem guard_setLane (index : Fin 4) : observerCount (.setLane index) = 2 := rfl
@[cil_guard] theorem guard_load64 : observerCount .load64 = 1 := rfl
@[cil_guard] theorem guard_store64 : observerCount .store64 = 2 := rfl
@[cil_guard] theorem guard_skipInit : observerCount .skipInit = 1 := rfl
@[cil_guard] theorem guard_asRef : observerCount .asRef = 1 := rfl

-- Operand counts of memory instructions, which `observerCount` defers to.
@[cil_guard] theorem guard_count_bigMul64 : CIL.MemoryOp.bigMul64.argumentCount = 3 := rfl
@[cil_guard] theorem guard_count_copyBlock (alignment : Nat) :
    (CIL.MemoryOp.copyBlock alignment).argumentCount = 3 := rfl
@[cil_guard] theorem guard_count_initBlock (alignment : Nat) :
    (CIL.MemoryOp.initBlock alignment).argumentCount = 3 := rfl
@[cil_guard] theorem guard_count_load128 : CIL.MemoryOp.load128.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_load256 : CIL.MemoryOp.load256.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_load512 : CIL.MemoryOp.load512.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_store128 : CIL.MemoryOp.store128.argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_store256 : CIL.MemoryOp.store256.argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_store512 : CIL.MemoryOp.store512.argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_init256 : CIL.MemoryOp.init256.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_asRef : CIL.MemoryOp.asRef.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_add (size : Nat) (signed : Bool) :
    (CIL.MemoryOp.add size signed).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_bitcast256 : CIL.MemoryOp.bitcast256.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_bitcastByteBool :
    CIL.MemoryOp.bitcastByteBool.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_bitcastValue (source target : CIL.SnapshotShape) :
    (CIL.MemoryOp.bitcastValue source target).argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_skipInit : CIL.MemoryOp.skipInit.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_staticAddress (bytes : List (BitVec 8)) :
    (CIL.MemoryOp.staticAddress bytes).argumentCount = 0 := rfl
@[cil_guard] theorem guard_count_staticValue (bytes : List (BitVec 8)) :
    (CIL.MemoryOp.staticValue bytes).argumentCount = 0 := rfl
@[cil_guard] theorem guard_count_createSpan (width : Nat) :
    (CIL.MemoryOp.createSpan width).argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_spanCreate : CIL.MemoryOp.spanCreate.argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_spanReference : CIL.MemoryOp.spanReference.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_spanItem (width : Nat) :
    (CIL.MemoryOp.spanItem width).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_spanLength : CIL.MemoryOp.spanLength.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_nullRef : CIL.MemoryOp.nullRef.argumentCount = 0 := rfl
@[cil_guard] theorem guard_count_isNullRef : CIL.MemoryOp.isNullRef.argumentCount = 1 := rfl

-- A loaded local must reach a bare value constructor, or no value-step equation matches
-- its consumer.
@[cil_guard] theorem localResult_narrow_i32 (kind : CIL.NarrowKind) (bits : CIL.W32) :
    localResult (.narrow kind) (.i32 bits) = .i32 (kind.extend bits) := rfl
@[cil_guard] theorem localResult_aggregate (size : Fin (2^64)) (value : CIL.Value) :
    localResult (.aggregate size) value = value := rfl
@[cil_guard] theorem localResult_byte (value : CIL.Value) : localResult .byte value = value := rfl
@[cil_guard] theorem localResult_word32 (value : CIL.Value) :
    localResult .word32 value = value := rfl
@[cil_guard] theorem localResult_word64 (value : CIL.Value) :
    localResult .word64 value = value := rfl
@[cil_guard] theorem localResult_vector128 (value : CIL.Value) :
    localResult .vector128 value = value := rfl
@[cil_guard] theorem localResult_vector256 (value : CIL.Value) :
    localResult .vector256 value = value := rfl
@[cil_guard] theorem localResult_vector512 (value : CIL.Value) :
    localResult .vector512 value = value := rfl
@[cil_guard] theorem localResult_reference (value : CIL.Value) :
    localResult .reference value = value := rfl

#print axioms localResult_narrow_i32
#print axioms localResult_aggregate
#print axioms localResult_byte
#print axioms localResult_word32
#print axioms localResult_word64
#print axioms localResult_vector128
#print axioms localResult_vector256
#print axioms localResult_vector512
#print axioms localResult_reference

end CIL.Safety
