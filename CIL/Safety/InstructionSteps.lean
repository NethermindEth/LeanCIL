import CIL.Safety.StepComposition
import CIL.Safety.GuardNormalization

/-!
# Instruction step equations

One `@[cil_instruction_step]` equation per `instruction` arm and operand shape for the 64-bit
word, field, reference and aggregate-initialization opcodes, so a step rewrites to that arm's
body at the level of `loadValue`, `storeValue`, `add`, `write` and `formValue`, where callers
state their memory facts, and never unfolds `instruction`. Other operand shapes keep the generic
`instructionStep` equations in `StepComposition`, which these outrank. The stepping tactics use
this set alongside `cil_step`; a hand-written `simp only [cil_step]` does not.
-/

namespace CIL.Safety

/-- Closes one instruction step equation through its generic `instructionStep` equation; the
    decided guard leaves the single matching arm. -/
local macro "instruction_step_proof " generic:ident : tactic => `(tactic| (
  rw [$generic:ident]
  simp only [instructionStep, instruction, cil_guard, unspecifiedOperands, List.take, List.any,
    Value.hasUnspecified, Bool.or_false, Bool.false_eq_true, ite_false, bind_assoc, pure_bind]
  all_goals first | rfl | (split <;> rfl)))

section InstructionEquations

variable (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)

-- 64-bit words through a reference.
/-- `load64` reads the word behind a writable reference. -/
@[cil_instruction_step high] theorem step_load64_reference_eq (reference : ManagedReference)
    (rest : List Value) :
    step body .load64 pc args frame (.reference reference :: rest) memory = do
      let value ← loadValue memory reference 8
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  instruction_step_proof step_load64_eq

/-- `load64` reads the word behind a readonly reference without write authority. -/
@[cil_instruction_step high] theorem step_load64_readOnlyReference_eq (reference : ManagedReference)
    (rest : List Value) :
    step body .load64 pc args frame (.readOnlyReference reference :: rest) memory = do
      let value ← loadValue memory reference 8
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  instruction_step_proof step_load64_eq

/-- `store64` writes an i64 through a writable reference. -/
@[cil_instruction_step high] theorem step_store64_reference_eq (bits : CIL.W64) (reference : ManagedReference)
    (rest : List Value) :
    step body .store64 pc args frame (.scalar (.i64 bits) :: .reference reference :: rest)
      memory = do
      let stored ← storeValue memory reference (.i64 bits)
      return .next (pc + 1) rest frame stored := by
  instruction_step_proof step_store64_eq

-- Fields of a referenced struct.
/-- A field load forms the field address, then reads it at the field's width. -/
@[cil_instruction_step high] theorem step_fieldAt_reference_eq (offset width : Nat) (signed : Bool)
    (reference : Reference) (rest : List Value) :
    step body (.fieldAt offset width signed) pc args frame
      (.reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let value ← loadValue memory (.address address) width signed
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  instruction_step_proof step_fieldAt_eq

/-- A field load through a readonly reference reads exactly as through a writable one. -/
@[cil_instruction_step high] theorem step_fieldAt_readOnlyReference_eq (offset width : Nat) (signed : Bool)
    (reference : Reference) (rest : List Value) :
    step body (.fieldAt offset width signed) pc args frame
      (.readOnlyReference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let value ← loadValue memory (.address address) width signed
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  instruction_step_proof step_fieldAt_eq

/-- A field address keeps a writable reference writable. -/
@[cil_instruction_step high] theorem step_fieldAddress_reference_eq (offset : Nat) (reference : Reference)
    (rest : List Value) :
    step body (.fieldAddress offset) pc args frame
      (.reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      return .next (pc + 1) (.reference (.address address) :: rest) frame memory := by
  instruction_step_proof step_fieldAddress_eq

/-- A field address of a readonly reference stays readonly. -/
@[cil_instruction_step high] theorem step_fieldAddress_readOnlyReference_eq (offset : Nat)
    (reference : Reference) (rest : List Value) :
    step body (.fieldAddress offset) pc args frame
      (.readOnlyReference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      return .next (pc + 1) (.readOnlyReference (.address address) :: rest) frame memory := by
  instruction_step_proof step_fieldAddress_eq

/-- An i32 field store of width 1, 2 or 4 writes the value's low bytes at the field address. -/
theorem step_setFieldAt_i32_eq (offset width : Nat) (narrow : width = 1 ∨ width = 2 ∨ width = 4)
    (bits : CIL.W32) (reference : Reference) (rest : List Value) :
    step body (.setFieldAt offset width) pc args frame
      (.scalar (.i32 bits) :: .reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let stored ← checkedAt (.address address) width
        (write memory address (numberBytes bits.toNat width) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored := by
  rcases narrow with rfl | rfl | rfl <;> instruction_step_proof step_setFieldAt_eq

/-- A one-byte field store. -/
@[cil_instruction_step high] theorem step_setFieldAt_i32_1_eq (offset : Nat) (bits : CIL.W32)
    (reference : Reference) (rest : List Value) :
    step body (.setFieldAt offset 1) pc args frame
      (.scalar (.i32 bits) :: .reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let stored ← checkedAt (.address address) 1
        (write memory address (numberBytes bits.toNat 1) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored :=
  step_setFieldAt_i32_eq body pc args frame memory offset 1 (.inl rfl) bits reference rest

/-- A two-byte field store. -/
@[cil_instruction_step high] theorem step_setFieldAt_i32_2_eq (offset : Nat) (bits : CIL.W32)
    (reference : Reference) (rest : List Value) :
    step body (.setFieldAt offset 2) pc args frame
      (.scalar (.i32 bits) :: .reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let stored ← checkedAt (.address address) 2
        (write memory address (numberBytes bits.toNat 2) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored :=
  step_setFieldAt_i32_eq body pc args frame memory offset 2 (.inr (.inl rfl)) bits reference rest

/-- A four-byte field store. -/
@[cil_instruction_step high] theorem step_setFieldAt_i32_4_eq (offset : Nat) (bits : CIL.W32)
    (reference : Reference) (rest : List Value) :
    step body (.setFieldAt offset 4) pc args frame
      (.scalar (.i32 bits) :: .reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let stored ← checkedAt (.address address) 4
        (write memory address (numberBytes bits.toNat 4) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored :=
  step_setFieldAt_i32_eq body pc args frame memory offset 4 (.inr (.inr rfl)) bits reference rest

/-- An eight-byte field store of an i64. -/
@[cil_instruction_step high] theorem step_setFieldAt_i64_eq (offset : Nat) (bits : CIL.W64)
    (reference : Reference) (rest : List Value) :
    step body (.setFieldAt offset 8) pc args frame
      (.scalar (.i64 bits) :: .reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let stored ← checkedAt (.address address) 8
        (write memory address (numberBytes bits.toNat 8) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored := by
  instruction_step_proof step_setFieldAt_eq

-- Fields of a struct value on the stack.
/-- A four-byte field of a struct value is read from its bytes, after a bounds check. -/
@[cil_instruction_step high] theorem step_fieldAt_aggregate_4_eq (offset : Nat) (signed : Bool)
    (bytes : List (BitVec 8)) (rest : List Value) :
    step body (.fieldAt offset 4 signed) pc args frame (.scalar (.aggregate bytes) :: rest)
      memory =
      if offset + 4 > bytes.length then .error .invalidState
      else .ok (.next (pc + 1)
        (.scalar (.i32 (BitVec.ofNat 32 (byteNumber ((bytes.drop offset).take 4)))) :: rest)
        frame memory) := by
  instruction_step_proof step_fieldAt_eq

/-- An eight-byte field of a struct value is read from its bytes, after a bounds check. -/
@[cil_instruction_step high] theorem step_fieldAt_aggregate_8_eq (offset : Nat) (signed : Bool)
    (bytes : List (BitVec 8)) (rest : List Value) :
    step body (.fieldAt offset 8 signed) pc args frame (.scalar (.aggregate bytes) :: rest)
      memory =
      if offset + 8 > bytes.length then .error .invalidState
      else .ok (.next (pc + 1)
        (.scalar (.i64 (BitVec.ofNat 64 (byteNumber ((bytes.drop offset).take 8)))) :: rest)
        frame memory) := by
  instruction_step_proof step_fieldAt_eq

-- Reference checks and struct initialization.
/-- `asRef` pushes the reference once it forms. -/
@[cil_instruction_step high] theorem step_asRef_reference_eq (reference : ManagedReference)
    (rest : List Value) :
    step body .asRef pc args frame (.reference reference :: rest) memory = do
      let value ← formValue memory reference
      return .next (pc + 1) (value :: rest) frame memory := by
  instruction_step_proof step_asRef_eq

/-- `skipInit` checks that the reference forms and pops it. -/
@[cil_instruction_step high] theorem step_skipInit_reference_eq (reference : ManagedReference)
    (rest : List Value) :
    step body .skipInit pc args frame (.reference reference :: rest) memory = do
      let _ ← formValue memory reference
      return .next (pc + 1) rest frame memory := by
  instruction_step_proof step_skipInit_eq

/-- `initobj` zeroes `size` bytes behind a writable reference. -/
@[cil_instruction_step high] theorem step_initAggregate_reference_eq (size : Nat)
    (reference : ManagedReference) (rest : List Value) :
    step body (.initAggregate size) pc args frame (.reference reference :: rest) memory = do
      let address ← referenceAt reference
      let stored ← checkedAt reference size
        (write memory address (List.replicate size 0) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored := by
  instruction_step_proof step_initAggregate_eq

end InstructionEquations

#print axioms step_load64_reference_eq
#print axioms step_load64_readOnlyReference_eq
#print axioms step_store64_reference_eq
#print axioms step_fieldAt_reference_eq
#print axioms step_fieldAt_readOnlyReference_eq
#print axioms step_fieldAddress_reference_eq
#print axioms step_fieldAddress_readOnlyReference_eq
#print axioms step_setFieldAt_i32_eq
#print axioms step_setFieldAt_i32_1_eq
#print axioms step_setFieldAt_i32_2_eq
#print axioms step_setFieldAt_i32_4_eq
#print axioms step_setFieldAt_i64_eq
#print axioms step_fieldAt_aggregate_4_eq
#print axioms step_fieldAt_aggregate_8_eq
#print axioms step_asRef_reference_eq
#print axioms step_skipInit_reference_eq
#print axioms step_initAggregate_reference_eq

end CIL.Safety
