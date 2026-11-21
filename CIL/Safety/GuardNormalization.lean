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
/-- Managed object references carry no unspecified vector bits. -/
@[cil_guard] theorem guard_managed_object (value : ManagedReference) :
    Value.hasUnspecified (.object value) = false := rfl
#print axioms guard_managed_object

@[cil_guard] theorem guard_span (reference : ManagedReference) (length : Nat) :
    Value.hasUnspecified (.span reference length) = false := rfl
/-- A span local's home carries no unspecified vector bits. -/
@[cil_guard] theorem guard_spanHome (slot : Nat) :
    Value.hasUnspecified (.spanHome slot) = false := rfl
#print axioms guard_spanHome

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

-- A memory operation that reads no span view takes its operands from the stack unchanged.
attribute [cil_guard] viewOperandCount
/-- With no view operands to read, the stack is the operation's operand list. -/
@[cil_guard] theorem viewOperands_zero (frame : Frame) (memory : Memory) (stack : List Value) :
    viewOperands frame memory 0 stack = .ok stack := rfl
#print axioms viewOperands_zero

-- The guard inspects only the top `count` stack operands.
@[cil_guard] theorem guard_operands_zero (stack : List Value) :
    unspecifiedOperands 0 stack = false := rfl
@[cil_guard] theorem guard_operands_nil (count : Nat) :
    unspecifiedOperands count [] = false := by simp [unspecifiedOperands]
@[cil_guard] theorem guard_operands_cons (count : Nat) (value : Value) (rest : List Value) :
    unspecifiedOperands (Nat.succ count) (value :: rest) =
      (value.hasUnspecified || unspecifiedOperands count rest) := rfl

-- How many stack operands each instruction observes.
/-- A signed division observes both of its operands. -/
@[cil_guard] theorem guard_div : observerCount .div = 2 := rfl
#print axioms guard_div
/-- An unsigned division observes both of its operands. -/
@[cil_guard] theorem guard_div_un : observerCount .div_un = 2 := rfl
#print axioms guard_div_un
/-- A signed remainder observes both of its operands. -/
@[cil_guard] theorem guard_rem : observerCount .rem = 2 := rfl
#print axioms guard_rem
/-- An unsigned remainder observes both of its operands. -/
@[cil_guard] theorem guard_rem_un : observerCount .rem_un = 2 := rfl
#print axioms guard_rem_un
/-- A signed checked addition observes both of its operands. -/
@[cil_guard] theorem guard_add_ovf : observerCount .add_ovf = 2 := rfl
#print axioms guard_add_ovf
/-- An unsigned checked addition observes both of its operands. -/
@[cil_guard] theorem guard_add_ovf_un : observerCount .add_ovf_un = 2 := rfl
#print axioms guard_add_ovf_un
/-- A signed checked subtraction observes both of its operands. -/
@[cil_guard] theorem guard_sub_ovf : observerCount .sub_ovf = 2 := rfl
#print axioms guard_sub_ovf
/-- An unsigned checked subtraction observes both of its operands. -/
@[cil_guard] theorem guard_sub_ovf_un : observerCount .sub_ovf_un = 2 := rfl
#print axioms guard_sub_ovf_un
/-- A signed checked multiplication observes both of its operands. -/
@[cil_guard] theorem guard_mul_ovf : observerCount .mul_ovf = 2 := rfl
#print axioms guard_mul_ovf
/-- An unsigned checked multiplication observes both of its operands. -/
@[cil_guard] theorem guard_mul_ovf_un : observerCount .mul_ovf_un = 2 := rfl
#print axioms guard_mul_ovf_un
/-- A checked conversion of a signed operand observes its one operand. -/
@[cil_guard] theorem guard_conv_ovf (target : CIL.ConvTarget) :
    observerCount (.conv_ovf target) = 1 := rfl
#print axioms guard_conv_ovf
/-- A checked conversion of an unsigned operand observes its one operand. -/
@[cil_guard] theorem guard_conv_ovf_un (target : CIL.ConvTarget) :
    observerCount (.conv_ovf_un target) = 1 := rfl
#print axioms guard_conv_ovf_un
@[cil_guard] theorem guard_ldarg (index : Nat) : observerCount (.ldarg index) = 0 := rfl
#print axioms guard_ldarg
@[cil_guard] theorem guard_starg (index : Nat) : observerCount (.starg index) = 0 := rfl
#print axioms guard_starg
@[cil_guard] theorem guard_ldarga (index : Nat) : observerCount (.ldarga index) = 0 := rfl
#print axioms guard_ldarga
/-- A call observes no operand before dispatch; the arm of its link checks them. -/
@[cil_guard] theorem guard_call (method : Extraction.MethodRef) (prefixes : CallPrefixes) :
    observerCount (.call method prefixes) = 0 := rfl
#print axioms guard_call
/-- A linked call checks its method's arguments. -/
@[cil_guard] theorem guard_call_linked (link : CIL.Link) (observed : Bool) :
    ((some link).isSome && observed) = observed := rfl
#print axioms guard_call_linked
/-- A call without a link leaves its operands to the model it runs. -/
@[cil_guard] theorem guard_call_unlinked (observed : Bool) :
    ((none : Option CIL.Link).isSome && observed) = false := rfl
#print axioms guard_call_unlinked
@[cil_guard] theorem guard_newobj (constructor : CIL.Extraction.MethodRef) :
    observerCount (.newobj constructor) = constructor.parameters.length := rfl
#print axioms guard_newobj

open Lean Meta in
/-- The argument count of a call's method as a numeral, when a closed term fixes its parameter
    list and receiver flag; a method a variable decides is left as it is. -/
dsimproc [cil_step, cil_guard] reduceArgumentCount (CIL.Extraction.MethodRef.argumentCount _) :=
  fun expression => do
    let_expr CIL.Extraction.MethodRef.argumentCount _ := expression | return .continue
    let count ← withDefault <| whnf expression
    match count.rawNatLit? <|> count.nat? with
    | some value => return .done (mkNatLit value)
    | none => return .continue
@[cil_guard] theorem guard_throw (exception : ExceptionType) :
    observerCount (.throw exception) = 0 := rfl
@[cil_guard] theorem guard_unadmitted (opcode : Nat) :
    observerCount (.unadmitted opcode) = 0 := rfl
/-- Return observes at most the first stack value, regardless of narrowing. -/
@[cil_guard] theorem guard_ret :
    observerCount .ret = 1 := rfl

#print axioms guard_ret
/-- The cpobj guard checks the operands observed by the storage operation. -/
@[cil_guard] theorem guard_cpobj (type : Extraction.TypeExpr) :
    observerCount (.cpobj type) = 2 := rfl
#print axioms guard_cpobj
/-- The initobj guard checks the operands observed by the storage operation. -/
@[cil_guard] theorem guard_initobj (type : Extraction.TypeExpr) :
    observerCount (.initobj type) = 1 := rfl
#print axioms guard_initobj
/-- The ldobj guard checks the operands observed by the storage operation. -/
@[cil_guard] theorem guard_ldobj (type : Extraction.TypeExpr) :
    observerCount (.ldobj type) = (if Extraction.spanLocal type then 0 else 1) := rfl
#print axioms guard_ldobj
/-- The stobj guard checks the operands observed by the storage operation. -/
@[cil_guard] theorem guard_stobj (type : Extraction.TypeExpr) :
    observerCount (.stobj type) = 2 := rfl
#print axioms guard_stobj
/-- The sizeof guard checks the operands observed by the storage operation. -/
@[cil_guard] theorem guard_sizeof (type : Extraction.TypeExpr) :
    observerCount (.sizeof type) = 0 := rfl
#print axioms guard_sizeof
@[cil_guard] theorem guard_ldind (kind : CIL.NumericKind) : observerCount (.ldind kind) = 1 := rfl
@[cil_guard] theorem guard_stind (kind : CIL.NumericKind) : observerCount (.stind kind) = 2 := rfl
@[cil_guard] theorem guard_ldlen : observerCount .ldlen = 1 := rfl
@[cil_guard] theorem guard_ldelem (kind : CIL.NumericKind) : observerCount (.ldelem kind) = 2 :=
  rfl
@[cil_guard] theorem guard_ldelem_ref : observerCount .ldelem_ref = 2 := rfl
@[cil_guard] theorem guard_stelem (kind : CIL.NumericKind) : observerCount (.stelem kind) = 3 :=
  rfl
@[cil_guard] theorem guard_stelem_ref : observerCount .stelem_ref = 3 := rfl
@[cil_guard] theorem guard_ldsfld (field : CIL.Extraction.FieldRef) :
    observerCount (.ldsfld field) = 0 := rfl
@[cil_guard] theorem guard_ldsflda (field : CIL.Extraction.FieldRef) :
    observerCount (.ldsflda field) = 0 := rfl
@[cil_guard] theorem guard_ldtoken (operand : CIL.TokenOperand) :
    observerCount (.ldtoken operand) = 0 := rfl
@[cil_guard] theorem guard_stsfld (field : CIL.Extraction.FieldRef) :
    observerCount (.stsfld field) = 1 := rfl

-- Operand counts of memory instructions, which `observerCount` defers to.
@[cil_guard] theorem guard_count_bigMul64 (signed : Bool) :
    (CIL.MemoryOp.bigMul64 signed).argumentCount = 3 := rfl
@[cil_guard] theorem guard_count_divRemOut (width : Nat) :
    (CIL.MemoryOp.divRemOut width).argumentCount = 3 := rfl
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
@[cil_guard] theorem guard_count_vector128Load :
    (CIL.MemoryOp.vector128Unsafe false false).argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_vector128LoadAt :
    (CIL.MemoryOp.vector128Unsafe false true).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_vector128Store :
    (CIL.MemoryOp.vector128Unsafe true false).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_vector128StoreAt :
    (CIL.MemoryOp.vector128Unsafe true true).argumentCount = 3 := rfl
@[cil_guard] theorem guard_count_asRef : CIL.MemoryOp.asRef.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_add (size : Nat) (signed : Bool) :
    (CIL.MemoryOp.add size signed).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_bitcastByteBool :
    CIL.MemoryOp.bitcastByteBool.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_bitcastValue (source target : CIL.SnapshotShape) :
    (CIL.MemoryOp.bitcastValue source target).argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_createSpan (width : Nat) :
    (CIL.MemoryOp.createSpan width).argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_spanCreate : CIL.MemoryOp.spanCreate.argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_spanReference : CIL.MemoryOp.spanReference.argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_spanItem (width : Nat) :
    (CIL.MemoryOp.spanItem width).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_spanLength : CIL.MemoryOp.spanLength.argumentCount = 1 := rfl
-- The remaining span and view operations, whose counts `viewOperandCount` also reads.
@[cil_guard] theorem guard_count_observeView (observation : CIL.ViewObservation) :
    (CIL.MemoryOp.observeView observation).argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_spanReinterpret (source target : Nat) (writable : Bool) :
    (CIL.MemoryOp.spanReinterpret source target writable).argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_spanCopy (width : Nat) (tryCopy : Bool) :
    (CIL.MemoryOp.spanCopy width tryCopy).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_spanClear (width : Nat) :
    (CIL.MemoryOp.spanFill width true).argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_spanFill (width : Nat) :
    (CIL.MemoryOp.spanFill width false).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_arrayFill (element : CIL.ArrayElement) :
    (CIL.MemoryOp.arrayFill element false).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_arrayFillCounted (element : CIL.ArrayElement) :
    (CIL.MemoryOp.arrayFill element true).argumentCount = 4 := rfl
@[cil_guard] theorem guard_count_spanEmpty (width : Nat) (writable : Bool) :
    (CIL.MemoryOp.spanEmpty width writable).argumentCount = 0 := rfl
@[cil_guard] theorem guard_count_spanFromReference (width : Nat) (writable : Bool) :
    (CIL.MemoryOp.spanFromReference width writable).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_spanSingleReference (width : Nat) (writable : Bool) :
    (CIL.MemoryOp.spanSingleReference width writable).argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_spanSlice : (CIL.MemoryOp.spanSlice false).argumentCount = 2 :=
  rfl
@[cil_guard] theorem guard_count_spanSliceCount :
    (CIL.MemoryOp.spanSlice true).argumentCount = 3 := rfl
@[cil_guard] theorem guard_count_spanReadOnly : CIL.MemoryOp.spanReadOnly.argumentCount = 1 :=
  rfl
@[cil_guard] theorem guard_count_arraySpan (element : CIL.ArrayElement) (writable : Bool) :
    (CIL.MemoryOp.arraySpan element writable .whole).argumentCount = 1 := rfl
@[cil_guard] theorem guard_count_arraySpanFrom (element : CIL.ArrayElement) (writable : Bool) :
    (CIL.MemoryOp.arraySpan element writable .fromStart).argumentCount = 2 := rfl
@[cil_guard] theorem guard_count_arraySpanCounted (element : CIL.ArrayElement) (writable : Bool) :
    (CIL.MemoryOp.arraySpan element writable .counted).argumentCount = 3 := rfl
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
