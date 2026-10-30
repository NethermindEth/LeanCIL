import CIL.Safety.StepComposition
import CIL.Safety.GuardNormalization

/-!
# Memory step equations

One `@[cil_step]` equation per `memoryInstruction` arm and operand shape, so a `.memory` step
rewrites to that arm's body and never unfolds `staticInstruction` or `memoryInstruction`.
The static-field arms keep `step_memory_eq`, which these outrank.
-/

namespace CIL.Safety

private theorem bind_ite {α β : Type} (c : Prop) [Decidable c] (a b : ExecutionResult α)
    (f : α → ExecutionResult β) : (if c then a else b) >>= f = if c then a >>= f else b >>= f := by
  split <;> rfl

/-- Closes one memory step equation through `step` and both memory dispatchers. Both
    dispatchers check the same operands, so a decided guard leaves one arm and no `if`. -/
local macro "memory_step_proof" : tactic => `(tactic| (
  simp only [step, staticInstruction, memoryInstruction, spanFillInstruction, spanCopyInstruction,
    otherMemoryInstruction, referenceAddInstruction, observerCount,
    CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    Bool.or_false, Bool.false_eq_true, ite_false, ite_true, CIL.offsetValue, cil_guard, bind_ite,
    bind_assoc, pure_bind]
  all_goals (repeat' split) <;>
    (try simp only [*, Bool.false_eq_true, ite_false, ite_true, bind_assoc, pure_bind]) <;> rfl))

section MemoryEquations

variable (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)

/-- Loading through a writable reference uses the existing width check and checked scalar read. -/
@[cil_step high] theorem step_loadScalar_reference_eq (width : Nat) (signed : Bool)
    (reference : ManagedReference) (rest : List Value) :
    step body (.loadScalar width signed) pc args frame (.reference reference :: rest) memory =
      if width = 1 || width = 2 || width = 4 || width = 8 then do
        let value ← loadValue memory reference width signed
        return .next (pc + 1) (.scalar value :: rest) frame memory
      else .error (.unsupported "Scalar memory width") := by
  rw [step_loadScalar_eq]
  simp only [instructionStep, instruction, cil_guard, unspecifiedOperands, List.take, List.any,
    Value.hasUnspecified, Bool.or_false, Bool.false_eq_true, ite_false, bind_ite,
    bind_assoc, pure_bind]
  rfl
#print axioms step_loadScalar_reference_eq

/-- A readonly reference permits the same checked read without acquiring write authority. -/
@[cil_step high] theorem step_loadScalar_readOnlyReference_eq (width : Nat) (signed : Bool)
    (reference : ManagedReference) (rest : List Value) :
    step body (.loadScalar width signed) pc args frame
      (.readOnlyReference reference :: rest) memory =
      if width = 1 || width = 2 || width = 4 || width = 8 then do
        let value ← loadValue memory reference width signed
        return .next (pc + 1) (.scalar value :: rest) frame memory
      else .error (.unsupported "Scalar memory width") := by
  rw [step_loadScalar_eq]
  simp only [instructionStep, instruction, cil_guard, unspecifiedOperands, List.take, List.any,
    Value.hasUnspecified, Bool.or_false, Bool.false_eq_true, ite_false, bind_ite,
    bind_assoc, pure_bind]
  rfl
#print axioms step_loadScalar_readOnlyReference_eq

/-- `bigMul64` stores the low 64 bits of the product through `low` and pushes the high 64. -/
@[cil_step high] theorem step_memory_bigMul64_eq (low : ManagedReference) (right left : CIL.W64)
    (rest : List Value) :
    step body (.memory .bigMul64) pc args frame
      (.reference low :: .scalar (.i64 right) :: .scalar (.i64 left) :: rest) memory = do
      let stored ← storeValue memory low (.i64 (left * right))
      return .next (pc + 1)
        (.scalar (.i64 (CIL.WideMultiply.high64 left right)) :: rest) frame stored := by
  memory_step_proof

/-- A zero-byte copy touches no memory, even through null references; otherwise overlapping
    source and destination regions are rejected. -/
@[cil_step high] theorem step_memory_copyBlock_eq (alignment : Nat) (count : CIL.W32)
    (source destination : ManagedReference) (rest : List Value) :
    step body (.memory (.copyBlock alignment)) pc args frame
      (.scalar (.i32 count) :: .reference source :: .reference destination :: rest) memory =
      if count.toNat = 0 then .ok (.next (pc + 1) rest frame memory) else do
        let src ← referenceAt source
        let dst ← referenceAt destination
        if src.allocation = dst.allocation && src.offset < dst.offset + count.toNat &&
            dst.offset < src.offset + count.toNat then
          .error (.unsupported "Overlapping block copy")
        else
          let bytes ← checkedAt source count.toNat (read memory src count.toNat alignment)
          let written ← checkedAt destination count.toNat (write memory dst bytes alignment)
          return .next (pc + 1) rest frame written := by
  memory_step_proof

/-- A zero-byte initialization touches no memory; otherwise, after a write access check, every
    byte becomes the low byte of `value`. -/
@[cil_step high] theorem step_memory_initBlock_eq (alignment : Nat) (count value : CIL.W32)
    (destination : ManagedReference) (rest : List Value) :
    step body (.memory (.initBlock alignment)) pc args frame
      (.scalar (.i32 count) :: .scalar (.i32 value) :: .reference destination :: rest) memory =
      if count.toNat = 0 then .ok (.next (pc + 1) rest frame memory) else do
        let dst ← referenceAt destination
        let _ ← checkedAt destination count.toNat (access memory dst count.toNat alignment true)
        let written ← checkedAt destination count.toNat
          (write memory dst (List.replicate count.toNat (value.setWidth 8)) alignment)
        return .next (pc + 1) rest frame written := by
  memory_step_proof

-- Vector loads and stores, one equation per stored value shape.
@[cil_step high] theorem step_memory_load128_eq (r : ManagedReference) (rest : List Value) :
    step body (.memory .load128) pc args frame (.reference r :: rest) memory = do
      let value ← loadValue memory r 16
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  memory_step_proof

@[cil_step high] theorem step_memory_load256_eq (r : ManagedReference) (rest : List Value) :
    step body (.memory .load256) pc args frame (.reference r :: rest) memory = do
      let value ← loadValue memory r 32
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  memory_step_proof

@[cil_step high] theorem step_memory_load512_eq (r : ManagedReference) (rest : List Value) :
    step body (.memory .load512) pc args frame (.reference r :: rest) memory = do
      let value ← loadValue memory r 64
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  memory_step_proof

@[cil_step high] theorem step_memory_store128_eq (bits : BitVec 128) (r : ManagedReference)
    (rest : List Value) :
    step body (.memory .store128) pc args frame
      (.scalar (.v128 bits) :: .reference r :: rest) memory = do
      let stored ← storeValue memory r (.v128 bits)
      return .next (pc + 1) rest frame stored := by
  memory_step_proof

@[cil_step high] theorem step_memory_store128_snapshot_eq (bytes : List (BitVec 8 × Bool))
    (r : ManagedReference) (rest : List Value) :
    step body (.memory .store128) pc args frame
      (.scalar (.snapshot .vector128 bytes) :: .reference r :: rest) memory = do
      let stored ← storeValue memory r (.snapshot .vector128 bytes)
      return .next (pc + 1) rest frame stored := by
  memory_step_proof

@[cil_step high] theorem step_memory_store256_eq (bits : BitVec 256) (r : ManagedReference)
    (rest : List Value) :
    step body (.memory .store256) pc args frame
      (.scalar (.v256 bits) :: .reference r :: rest) memory = do
      let stored ← storeValue memory r (.v256 bits)
      return .next (pc + 1) rest frame stored := by
  memory_step_proof

@[cil_step high] theorem step_memory_store256_snapshot_eq (bytes : List (BitVec 8 × Bool))
    (r : ManagedReference) (rest : List Value) :
    step body (.memory .store256) pc args frame
      (.scalar (.snapshot .vector256 bytes) :: .reference r :: rest) memory = do
      let stored ← storeValue memory r (.snapshot .vector256 bytes)
      return .next (pc + 1) rest frame stored := by
  memory_step_proof

@[cil_step high] theorem step_memory_store512_eq (bits : BitVec 512) (r : ManagedReference)
    (rest : List Value) :
    step body (.memory .store512) pc args frame
      (.scalar (.v512 bits) :: .reference r :: rest) memory = do
      let stored ← storeValue memory r (.v512 bits)
      return .next (pc + 1) rest frame stored := by
  memory_step_proof

@[cil_step high] theorem step_memory_store512_snapshot_eq (bytes : List (BitVec 8 × Bool))
    (r : ManagedReference) (rest : List Value) :
    step body (.memory .store512) pc args frame
      (.scalar (.snapshot .vector512 bytes) :: .reference r :: rest) memory = do
      let stored ← storeValue memory r (.snapshot .vector512 bytes)
      return .next (pc + 1) rest frame stored := by
  memory_step_proof

@[cil_step high] theorem step_memory_init256_eq (r : ManagedReference) (rest : List Value) :
    step body (.memory .init256) pc args frame (.reference r :: rest) memory = do
      let stored ← storeValue memory r (.v256 0)
      return .next (pc + 1) rest frame stored := by
  memory_step_proof

-- References, pointer arithmetic and bit casts.
@[cil_step high] theorem step_memory_asRef_eq (r : ManagedReference) (rest : List Value) :
    step body (.memory .asRef) pc args frame (.reference r :: rest) memory = do
      let value ← formValue memory r
      return .next (pc + 1) (value :: rest) frame memory := by
  memory_step_proof

/-- Commuted reference offsets reuse the scalar-first memory step equations. -/
@[cil_step high] theorem step_memory_add_commuted_eq (size : Nat) (signed : Bool)
    (reference : ManagedReference) (offset : CIL.Value) (rest : List Value) :
    step body (.memory (.add size signed)) pc args frame
      (.reference reference :: .scalar offset :: rest) memory =
    step body (.memory (.add size signed)) pc args frame
      (.scalar offset :: .reference reference :: rest) memory := by
  rfl
#print axioms step_memory_add_commuted_eq

-- One equation per `offsetValue` shape, so the offset is a term and needs no side condition.
@[cil_step high] theorem step_memory_add_signed_i32_eq (size : Nat) (offset : CIL.W32)
    (r : ManagedReference) (rest : List Value) :
    step body (.memory (.add size true)) pc args frame
      (.scalar (.i32 offset) :: .reference r :: rest) memory = do
      let address ← referenceAt r
      let result ← checkedAt r 0 (add memory address size (BitVec.ofInt 64 offset.toInt))
      return .next (pc + 1) (.reference (.address result) :: rest) frame memory := by
  memory_step_proof

@[cil_step high] theorem step_memory_add_signed_i64_eq (size : Nat) (offset : CIL.W64)
    (r : ManagedReference) (rest : List Value) :
    step body (.memory (.add size true)) pc args frame
      (.scalar (.i64 offset) :: .reference r :: rest) memory = do
      let address ← referenceAt r
      let result ← checkedAt r 0 (add memory address size (BitVec.ofInt 64 offset.toInt))
      return .next (pc + 1) (.reference (.address result) :: rest) frame memory := by
  memory_step_proof

@[cil_step high] theorem step_memory_add_unsigned_i64_eq (size : Nat) (offset : CIL.W64)
    (r : ManagedReference) (rest : List Value) :
    step body (.memory (.add size false)) pc args frame
      (.scalar (.i64 offset) :: .reference r :: rest) memory = do
      let address ← referenceAt r
      let result ← checkedAt r 0 (add memory address size (BitVec.ofInt 64 (offset.toNat : Int)))
      return .next (pc + 1) (.reference (.address result) :: rest) frame memory := by
  memory_step_proof

@[cil_step high] theorem step_memory_bitcast256_eq (bits : BitVec 256) (rest : List Value) :
    step body (.memory .bitcast256) pc args frame (.scalar (.v256 bits) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.v256 bits) :: rest) frame memory) := by
  memory_step_proof

-- The operand is any scalar, so the guard stays until the caller's value decides it.
@[cil_step high] theorem step_memory_bitcastValue_eq (source target : CIL.SnapshotShape)
    (value : CIL.Value) (rest : List Value) :
    step body (.memory (.bitcastValue source target)) pc args frame (.scalar value :: rest) memory =
      if value.hasUnspecified then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else do
        let cast ← bitcastValue source target value
        return .next (pc + 1) (.scalar cast :: rest) frame memory := by
  memory_step_proof

-- A byte reinterpreted as a Boolean must be 0 or 1.
@[cil_step high] theorem step_memory_bitcastByteBool_i32_eq (bits : CIL.W32) (rest : List Value) :
    step body (.memory .bitcastByteBool) pc args frame (.scalar (.i32 bits) :: rest) memory =
      if bits.toNat ≤ 1 then .ok (.next (pc + 1) (.scalar (.i32 bits) :: rest) frame memory)
      else .error (.unsupported "Noncanonical Boolean representation") := by
  memory_step_proof

@[cil_step high] theorem step_memory_bitcastByteBool_i8_eq (bits : BitVec 8) (rest : List Value) :
    step body (.memory .bitcastByteBool) pc args frame (.scalar (.i8 bits) :: rest) memory =
      if bits.toNat ≤ 1 then
        .ok (.next (pc + 1) (.scalar (.i32 (bits.zeroExtend 32)) :: rest) frame memory)
      else .error (.unsupported "Noncanonical Boolean representation") := by
  memory_step_proof

@[cil_step high] theorem step_memory_skipInit_eq (r : ManagedReference) (rest : List Value) :
    step body (.memory .skipInit) pc args frame (.reference r :: rest) memory = do
      let _ ← formValue memory r
      return .next (pc + 1) rest frame memory := by
  memory_step_proof

-- Spans.
@[cil_step high] theorem step_memory_spanReference_eq (r : ManagedReference) (length : Nat)
    (rest : List Value) :
    step body (.memory .spanReference) pc args frame (.span r length :: rest) memory = do
      let value ← formValue memory r
      return .next (pc + 1) (value :: rest) frame memory := by
  memory_step_proof

/-- `MemoryMarshal.GetReference` over a writable view returns its start reference, even when
    the view is empty; it validates the view's extent but makes no access. -/
@[cil_step high] theorem step_memory_spanReference_view_eq (reference : ManagedReference)
    (length width : Nat) (rest : List Value) :
    step body (.memory .spanReference) pc args frame
      (.bufferSpan ⟨reference, length, width, true⟩ :: rest) memory = do
      let _ ← checkedAt reference 0 (SpanView.validate ⟨reference, length, width, true⟩ memory)
      let value ← formValue memory reference
      return .next (pc + 1) (value :: rest) frame memory := by
  simp only [step, staticInstruction, memoryInstruction, otherMemoryInstruction, observerCount,
    CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    Bool.or_false, Bool.false_eq_true, ite_false, cil_guard, bind_ite, bind_assoc, pure_bind]
  all_goals (repeat' split) <;> first
    | exact absurd trivial (by assumption)
    | ((try simp only [*]) <;> rfl)

/-- `MemoryMarshal.GetReference` over a readonly view returns its start reference restricted
    to reads, even when the view is empty; it validates the view's extent but makes no access. -/
@[cil_step high] theorem step_memory_spanReference_readOnlyView_eq (reference : ManagedReference)
    (length width : Nat) (rest : List Value) :
    step body (.memory .spanReference) pc args frame
      (.bufferSpan ⟨reference, length, width, false⟩ :: rest) memory = do
      let _ ← checkedAt reference 0 (SpanView.validate ⟨reference, length, width, false⟩ memory)
      let _ ← formValue memory reference
      return .next (pc + 1) (.readOnlyReference reference :: rest) frame memory := by
  simp only [step, staticInstruction, memoryInstruction, otherMemoryInstruction, observerCount,
    CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    Bool.or_false, Bool.false_eq_true, ite_false, cil_guard, bind_ite, bind_assoc, pure_bind]
  all_goals (repeat' split) <;> first
    | exact absurd trivial (by assumption)
    | ((try simp only [*]) <;> rfl)

/-- The address of element `index`; an index that is negative or not below `length` throws
    `IndexOutOfRangeException`. -/
@[cil_step high] theorem step_memory_spanItem_eq (width : Nat) (index : CIL.W32)
    (r : ManagedReference) (length : Nat) (rest : List Value) :
    step body (.memory (.spanItem width)) pc args frame
      (.scalar (.i32 index) :: .span r length :: rest) memory =
      if index.toNat < length then do
        let address ← referenceAt r
        let result ← checkedAt r 0 (add memory address width (BitVec.ofNat 64 index.toNat))
        return .next (pc + 1) (.reference (.address result) :: rest) frame memory
      else .error (.thrown "System.IndexOutOfRangeException") := by
  memory_step_proof

@[cil_step high] theorem step_memory_spanLength_eq (r : ManagedReference) (length : Nat)
    (rest : List Value) :
    step body (.memory .spanLength) pc args frame (.span r length :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 (BitVec.ofNat 32 length)) :: rest) frame memory) := by
  memory_step_proof

/-- A buffer span's length retains its validation obligation and does not read its bytes. -/
@[cil_step high] theorem step_memory_bufferSpanLength_eq (view : SpanView) (rest : List Value) :
    step body (.memory .spanLength) pc args frame (.bufferSpan view :: rest) memory = do
      let _ ← checkedAt view.reference 0 (view.validate memory)
      return .next (pc + 1)
        (.scalar (.i32 (BitVec.ofNat 32 view.length)) :: rest) frame memory := by
  memory_step_proof
#print axioms step_memory_bufferSpanLength_eq

/-- A suffix slice checks the starting index and preserves the span's storage and capability. -/
@[cil_step high] theorem step_memory_bufferSpanSlice_eq (view : SpanView)
    (start : CIL.W32) (rest : List Value) :
    step body (.memory (.spanSlice false)) pc args frame
      (.scalar (.i32 start) :: .bufferSpan view :: rest) memory = do
      if start.toNat ≤ view.length then pure ()
        else .error (.thrown "System.ArgumentOutOfRangeException")
      let sliced ← checkedAt view.reference 0
        (view.slice memory start.toNat (view.length - start.toNat))
      return .next (pc + 1) (.bufferSpan sliced :: rest) frame memory := by
  memory_step_proof
#print axioms step_memory_bufferSpanSlice_eq

/-- A counted slice retains both range checks and the checked view-construction result. -/
@[cil_step high] theorem step_memory_bufferSpanSliceCount_eq (view : SpanView)
    (start length : CIL.W32) (rest : List Value) :
    step body (.memory (.spanSlice true)) pc args frame
      (.scalar (.i32 length) :: .scalar (.i32 start) :: .bufferSpan view :: rest) memory = do
      if start.toNat ≤ view.length && length.toNat ≤ view.length - start.toNat then pure ()
        else .error (.thrown "System.ArgumentOutOfRangeException")
      let sliced ← checkedAt view.reference 0 (view.slice memory start.toNat length.toNat)
      return .next (pc + 1) (.bufferSpan sliced :: rest) frame memory := by
  memory_step_proof
#print axioms step_memory_bufferSpanSliceCount_eq

/-- Buffer indexing keeps width, bounds and memory checks before returning a restricted address. -/
@[cil_step high] theorem step_memory_bufferSpanItem_eq (view : SpanView)
    (width : Nat) (index : CIL.W32) (rest : List Value) :
    step body (.memory (.spanItem width)) pc args frame
      (.scalar (.i32 index) :: .bufferSpan view :: rest) memory = do
      if width == view.width then pure () else .error .invalidState
      if index.toNat < view.length then pure ()
        else .error (.thrown "System.IndexOutOfRangeException")
      let reference ← checkedAt view.reference width (view.element memory index.toNat)
      return .next (pc + 1)
        ((if view.writable then .reference (.address reference)
          else .readOnlyReference (.address reference)) :: rest) frame memory := by
  memory_step_proof
#print axioms step_memory_bufferSpanItem_eq

-- Null references; `isNullRef` makes no access, so it answers for expired references too.
@[cil_step high] theorem step_memory_nullRef_eq (stack : List Value) :
    step body (.memory .nullRef) pc args frame stack memory =
      .ok (.next (pc + 1) (.reference .null :: stack) frame memory) := by
  memory_step_proof

@[cil_step high] theorem step_memory_isNullRef_null_eq (rest : List Value) :
    step body (.memory .isNullRef) pc args frame (.reference .null :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 1) :: rest) frame memory) := by
  memory_step_proof

@[cil_step high] theorem step_memory_isNullRef_address_eq (r : Reference) (rest : List Value) :
    step body (.memory .isNullRef) pc args frame (.reference (.address r) :: rest) memory =
      .ok (.next (pc + 1) (.scalar (.i32 0) :: rest) frame memory) := by
  memory_step_proof

end MemoryEquations

#print axioms step_memory_bigMul64_eq
#print axioms step_memory_copyBlock_eq
#print axioms step_memory_initBlock_eq
#print axioms step_memory_load128_eq
#print axioms step_memory_load256_eq
#print axioms step_memory_load512_eq
#print axioms step_memory_store128_eq
#print axioms step_memory_store128_snapshot_eq
#print axioms step_memory_store256_eq
#print axioms step_memory_store256_snapshot_eq
#print axioms step_memory_store512_eq
#print axioms step_memory_store512_snapshot_eq
#print axioms step_memory_init256_eq
#print axioms step_memory_asRef_eq
#print axioms step_memory_add_signed_i32_eq
#print axioms step_memory_add_signed_i64_eq
#print axioms step_memory_add_unsigned_i64_eq
#print axioms step_memory_bitcast256_eq
#print axioms step_memory_bitcastValue_eq
#print axioms step_memory_bitcastByteBool_i32_eq
#print axioms step_memory_bitcastByteBool_i8_eq
#print axioms step_memory_skipInit_eq
#print axioms step_memory_spanReference_eq
#print axioms step_memory_spanReference_view_eq
#print axioms step_memory_spanReference_readOnlyView_eq
#print axioms step_memory_spanItem_eq
#print axioms step_memory_spanLength_eq
#print axioms step_memory_nullRef_eq
#print axioms step_memory_isNullRef_null_eq
#print axioms step_memory_isNullRef_address_eq

end CIL.Safety
