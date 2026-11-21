import CIL.Safety.ValueSteps

/-!
# Instruction step equations

One `@[cil_instruction_step]` equation per `instruction` arm and operand shape for the indirect
integer, handler-table, scalar-store, field, reference and aggregate-initialization opcodes, so a
step rewrites to that arm's body at the level of `loadValue`, `storeValue`, `add`, `write` and
`formValue`, where callers state their memory facts, and never unfolds `instruction`. Other
operand shapes keep the generic `instructionStep` equations in `StepComposition`, which these
outrank. The stepping tactics use this set alongside `cil_step`, and `cil_instruction_step_goal`
lists its opcodes; a hand-written `simp only [cil_step]` does not use it.
-/

namespace CIL.Safety

/-- Closes one instruction step equation through its generic `instructionStep` equation; the
    decided guard leaves the single matching arm. -/
local macro "instruction_step_proof " generic:ident : tactic => `(tactic| (
  rw [$generic:ident]
  simp only [instructionStep, instruction, transferValues, elementInstruction, cil_guard, unspecifiedOperands,
    List.take, List.any,
    Value.hasUnspecified, Bool.or_false, Bool.false_eq_true, ite_false, bind_assoc, pure_bind]
  all_goals first | rfl | (split <;> rfl)))

section InstructionEquations

variable (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)

-- Indirect integer loads and stores.
/-- `ldind` reads its kind's width behind a writable reference, sign-extending a narrow signed
    kind. -/
@[cil_instruction_step high]
theorem step_ldind_reference_eq (kind : CIL.NumericKind) (reference : ManagedReference)
    (rest : List Value) :
    step body (.ldind kind) pc args frame (.reference reference :: rest) memory = do
      let value ← loadValue memory reference kind.width kind.signed
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  instruction_step_proof step_ldind_eq

/-- `ldind` reads behind a readonly reference exactly as behind a writable one. -/
@[cil_instruction_step high]
theorem step_ldind_readOnlyReference_eq (kind : CIL.NumericKind) (reference : ManagedReference)
    (rest : List Value) :
    step body (.ldind kind) pc args frame (.readOnlyReference reference :: rest) memory = do
      let value ← loadValue memory reference kind.width kind.signed
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  instruction_step_proof step_ldind_eq

/-- A native `ldind` on a method table cursor loads the authenticated entry it names. -/
@[cil_instruction_step high]
theorem step_ldind_table_eq (table : CIL.MethodTable) (rest : List Value) :
    step body (.ldind .i) pc args frame (.methodTable table :: rest) memory = do
      let pointer ← checkedAt .null nativeMethodWidth (loadNativeTable table memory)
      return .next (pc + 1) (.methodPointer pointer :: rest) frame memory := by
  instruction_step_proof step_ldind_eq

-- Handler table reads.
/-- `ldlen` of a managed handler table pushes its entry count. -/
@[cil_instruction_step high]
theorem step_ldlen_table_eq (table : CIL.MethodTable) (rest : List Value) :
    step body .ldlen pc args frame (.methodTable table :: rest) memory = do
      let length ← methodTableLength table
      return .next (pc + 1) (.scalar length :: rest) frame memory := by
  instruction_step_proof step_ldlen_eq

/-- `ldelem.i` of a managed handler table at an int32 index pushes the method pointer there. -/
@[cil_instruction_step high]
theorem step_ldelem_i_table_eq (index : CIL.W32) (table : CIL.MethodTable)
    (rest : List Value) :
    step body (.ldelem .i) pc args frame (.scalar (.i32 index) :: .methodTable table :: rest)
      memory = do
      let pointer ← methodTableElement table (.i32 index) memory
      return .next (pc + 1) (.methodPointer pointer :: rest) frame memory := by
  instruction_step_proof step_ldelem_eq

/-- `stind.i8` writes an i64 through a writable reference. -/
@[cil_instruction_step high]
theorem step_stind_i8_eq (bits : CIL.W64) (reference : ManagedReference) (rest : List Value) :
    step body (.stind .i8) pc args frame (.scalar (.i64 bits) :: .reference reference :: rest)
      memory = do
      let stored ← storeValue memory reference (.i64 bits)
      return .next (pc + 1) rest frame stored := by
  instruction_step_proof step_stind_eq

/-- `stind.i` writes a native int, an i64 on every admitted profile, as `stind.i8` does. -/
@[cil_instruction_step high]
theorem step_stind_i_eq (bits : CIL.W64) (reference : ManagedReference) (rest : List Value) :
    step body (.stind .i) pc args frame (.scalar (.i64 bits) :: .reference reference :: rest)
      memory = do
      let stored ← storeValue memory reference (.i64 bits)
      return .next (pc + 1) rest frame stored := by
  instruction_step_proof step_stind_eq

/-- A one-, two- or four-byte `stind` writes the low bytes of an i32 through the reference. -/
theorem step_stind_i32_eq (kind : CIL.NumericKind) (narrow : kind.width ≠ 8) (bits : CIL.W32)
    (reference : ManagedReference) (rest : List Value) :
    step body (.stind kind) pc args frame (.scalar (.i32 bits) :: .reference reference :: rest)
      memory = do
      let address ← referenceAt reference
      let stored ← checkedAt reference kind.width
        (write memory address (numberBytes bits.toNat kind.width) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored := by
  cases kind <;> first | exact absurd rfl narrow | instruction_step_proof step_stind_eq

-- Scalar stores through a reference.
/-- An i32 store of width 1, 2 or 4 writes the value's low bytes through the reference. -/
theorem step_storeScalar_i32_eq (width : Nat) (narrow : width = 1 ∨ width = 2 ∨ width = 4)
    (bits : CIL.W32) (reference : ManagedReference) (rest : List Value) :
    step body (.storeScalar width) pc args frame
      (.scalar (.i32 bits) :: .reference reference :: rest) memory = do
      let address ← referenceAt reference
      let stored ← checkedAt reference width
        (write memory address (numberBytes bits.toNat width) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored := by
  rcases narrow with rfl | rfl | rfl <;> instruction_step_proof step_storeScalar_eq

/-- A one-byte scalar store. -/
@[cil_instruction_step high]
theorem step_storeScalar_i32_1_eq (bits : CIL.W32)
    (reference : ManagedReference) (rest : List Value) :
    step body (.storeScalar 1) pc args frame
      (.scalar (.i32 bits) :: .reference reference :: rest) memory = do
      let address ← referenceAt reference
      let stored ← checkedAt reference 1
        (write memory address (numberBytes bits.toNat 1) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored :=
  step_storeScalar_i32_eq body pc args frame memory 1 (.inl rfl) bits reference rest

/-- A two-byte scalar store. -/
@[cil_instruction_step high]
theorem step_storeScalar_i32_2_eq (bits : CIL.W32)
    (reference : ManagedReference) (rest : List Value) :
    step body (.storeScalar 2) pc args frame
      (.scalar (.i32 bits) :: .reference reference :: rest) memory = do
      let address ← referenceAt reference
      let stored ← checkedAt reference 2
        (write memory address (numberBytes bits.toNat 2) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored :=
  step_storeScalar_i32_eq body pc args frame memory 2 (.inr (.inl rfl)) bits reference rest

/-- A four-byte scalar store. -/
@[cil_instruction_step high]
theorem step_storeScalar_i32_4_eq (bits : CIL.W32)
    (reference : ManagedReference) (rest : List Value) :
    step body (.storeScalar 4) pc args frame
      (.scalar (.i32 bits) :: .reference reference :: rest) memory = do
      let address ← referenceAt reference
      let stored ← checkedAt reference 4
        (write memory address (numberBytes bits.toNat 4) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored :=
  step_storeScalar_i32_eq body pc args frame memory 4 (.inr (.inr rfl)) bits reference rest

/-- An eight-byte scalar store of an i64. -/
@[cil_instruction_step high]
theorem step_storeScalar_i64_eq (bits : CIL.W64)
    (reference : ManagedReference) (rest : List Value) :
    step body (.storeScalar 8) pc args frame
      (.scalar (.i64 bits) :: .reference reference :: rest) memory = do
      let address ← referenceAt reference
      let stored ← checkedAt reference 8
        (write memory address (numberBytes bits.toNat 8) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored := by
  instruction_step_proof step_storeScalar_eq

-- Fields of a referenced struct.
/-- A field load forms the field address, then reads it at the field's width. -/
@[cil_instruction_step high]
theorem step_fieldAt_reference_eq (offset width : Nat) (signed : Bool)
    (reference : Reference) (rest : List Value) :
    step body (.fieldAt offset width signed) pc args frame
      (.reference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let value ← loadValue memory (.address address) width signed
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  instruction_step_proof step_fieldAt_eq

/-- A field load through a readonly reference reads exactly as through a writable one. -/
@[cil_instruction_step high]
theorem step_fieldAt_readOnlyReference_eq (offset width : Nat) (signed : Bool)
    (reference : Reference) (rest : List Value) :
    step body (.fieldAt offset width signed) pc args frame
      (.readOnlyReference (.address reference) :: rest) memory = do
      let address ← checkedAt (.address reference) 0
        (add memory reference 1 (BitVec.ofNat 64 offset))
      let value ← loadValue memory (.address address) width signed
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  instruction_step_proof step_fieldAt_eq

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
@[cil_instruction_step high]
theorem step_setFieldAt_i32_1_eq (offset : Nat) (bits : CIL.W32)
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
@[cil_instruction_step high]
theorem step_setFieldAt_i32_2_eq (offset : Nat) (bits : CIL.W32)
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
@[cil_instruction_step high]
theorem step_setFieldAt_i32_4_eq (offset : Nat) (bits : CIL.W32)
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
@[cil_instruction_step high]
theorem step_setFieldAt_i64_eq (offset : Nat) (bits : CIL.W64)
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
@[cil_instruction_step high]
theorem step_fieldAt_aggregate_4_eq (offset : Nat) (signed : Bool)
    (bytes : List (BitVec 8)) (rest : List Value) :
    step body (.fieldAt offset 4 signed) pc args frame (.scalar (.aggregate bytes) :: rest)
      memory =
      if offset + 4 > bytes.length then .error .invalidState
      else .ok (.next (pc + 1)
        (.scalar (.i32 (BitVec.ofNat 32 (byteNumber ((bytes.drop offset).take 4)))) :: rest)
        frame memory) := by
  instruction_step_proof step_fieldAt_eq

/-- An eight-byte field of a struct value is read from its bytes, after a bounds check. -/
@[cil_instruction_step high]
theorem step_fieldAt_aggregate_8_eq (offset : Nat) (signed : Bool)
    (bytes : List (BitVec 8)) (rest : List Value) :
    step body (.fieldAt offset 8 signed) pc args frame (.scalar (.aggregate bytes) :: rest)
      memory =
      if offset + 8 > bytes.length then .error .invalidState
      else .ok (.next (pc + 1)
        (.scalar (.i64 (BitVec.ofNat 64 (byteNumber ((bytes.drop offset).take 8)))) :: rest)
        frame memory) := by
  instruction_step_proof step_fieldAt_eq

/-- A nested struct field of a struct value is the field's bytes, after a bounds check. -/
@[cil_instruction_step high]
theorem step_ldfld_aggregate_value_eq (field : Extraction.FieldRef) (offset size : Nat)
    (shape : body.fieldShape field = .aggregate offset size)
    (bytes : List (BitVec 8)) (rest : List Value) :
    step body (.ldfld field) pc args frame (.scalar (.aggregate bytes) :: rest)
      memory =
      if offset + size > bytes.length then .error .invalidState
      else .ok (.next (pc + 1)
        (.scalar (.aggregate ((bytes.drop offset).take size)) :: rest) frame memory) := by
  rw [step_ldfld_aggregate_eq body pc args frame memory field offset size shape]
  simp only [loadAggregateField, cil_guard, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    Bool.or_false, Bool.false_eq_true, ite_false]
  split <;> rfl

/-- A nested struct field of a struct snapshot is the slice of its bytes and flags, a plain struct
    value when all of them are initialized, after a bounds check. -/
@[cil_instruction_step high]
theorem step_ldfld_aggregate_snapshot_eq (field : Extraction.FieldRef) (offset size : Nat)
    (shape : body.fieldShape field = .aggregate offset size) (total : Nat)
    (bytes : List (BitVec 8 × Bool)) (rest : List Value) :
    step body (.ldfld field) pc args frame
      (.scalar (.snapshot (.aggregate total) bytes) :: rest) memory =
      if bytes.length != total || offset + size > total then .error .invalidState
      else .ok (.next (pc + 1)
        (.scalar (snapshotValue (.aggregate size) ((bytes.drop offset).take size)) :: rest)
        frame memory) := by
  rw [step_ldfld_aggregate_eq body pc args frame memory field offset size shape]
  simp only [loadAggregateField, cil_guard, unspecifiedOperands, List.take, List.any, Value.hasUnspecified,
    Bool.or_false, Bool.false_eq_true, ite_false]
  split <;> rfl

-- Reference checks and struct initialization.
/-- `initobj` zeroes `size` bytes behind a writable reference. -/
@[cil_instruction_step high]
theorem step_initobj_reference_eq {type : Extraction.TypeExpr} {size : Nat}
    (width : (body.valueShape type).size? = some size)
    (reference : ManagedReference) (rest : List Value) :
    step body (.initobj type) pc args frame (.reference reference :: rest) memory = do
      let address ← referenceAt reference
      let stored ← checkedAt reference size
        (write memory address (List.replicate size 0) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame stored := by
  rw [step_initobj_eq body pc args frame memory width]
  simp [initializeBytes, unspecifiedOperands, Value.hasUnspecified, bind_assoc]

end InstructionEquations

open Lean Meta in
/-- The storage equation at a named operand whose checked shape supplies the byte width. -/
private def objectSizeStep (expression : Expr) : SimpM Simp.Step := do
  let_expr CIL.Safety.step body operation pc args frame stack memory := expression
    | return .continue
  let (opcode, #[type]) := operation.getAppFnArgs | return .continue
  let read := mkApp2 (mkConst ``CIL.Method.valueShape) body type
  let some (.done shared) ← ResolutionFacts.sharedShape? ``CIL.Method.valueShape read
    | return .continue
  let some proof := shared.proof? | return .continue
  let size ← match shared.expr.getAppFnArgs with
    | (``CIL.ValueShape.primitive, #[width, _]) | (``CIL.ValueShape.aggregate, #[width])
    | (``CIL.ValueShape.vector, #[width]) => pure width
    | _ => return .continue
  let width ← mkCongrArg (mkConst ``CIL.ValueShape.size?) proof
  let leading := #[body, pc, args, frame, memory, type, size, width]
  if opcode == ``CIL.Instruction.initobj then
    if let some (_, head, rest) := stack.app3? ``List.cons then
      if let some reference := head.app1? ``Value.reference then
        return ← equationStep (mkAppN (mkConst ``step_initobj_reference_eq)
          (leading ++ #[reference, rest]))
  let equation := if opcode == ``CIL.Instruction.initobj then ``step_initobj_eq
    else if opcode == ``CIL.Instruction.cpobj then ``step_cpobj_eq else ``step_sizeof_eq
  equationStep (mkAppN (mkConst equation) (leading.push stack))

/-- A typed initialization steps at the byte width of its named operand. -/
simproc [cil_instruction_step] reduceObjectInit (step _ (.initobj _) _ _ _ _ _) := objectSizeStep

/-- A typed copy steps at the byte width of its named operand. -/
simproc [cil_instruction_step] reduceObjectCopy (step _ (.cpobj _) _ _ _ _ _) := objectSizeStep

/-- A size instruction pushes the byte width of its named operand. -/
simproc [cil_instruction_step] reduceObjectSize (step _ (.sizeof _) _ _ _ _ _) := objectSizeStep

#print axioms step_ldind_reference_eq
#print axioms step_ldind_readOnlyReference_eq
#print axioms step_ldind_table_eq
#print axioms step_ldlen_table_eq
#print axioms step_ldelem_i_table_eq
#print axioms step_stind_i8_eq
#print axioms step_stind_i_eq
#print axioms step_stind_i32_eq
#print axioms step_storeScalar_i32_eq
#print axioms step_storeScalar_i32_1_eq
#print axioms step_storeScalar_i32_2_eq
#print axioms step_storeScalar_i32_4_eq
#print axioms step_storeScalar_i64_eq
#print axioms step_fieldAt_reference_eq
#print axioms step_fieldAt_readOnlyReference_eq
#print axioms step_setFieldAt_i32_eq
#print axioms step_setFieldAt_i32_1_eq
#print axioms step_setFieldAt_i32_2_eq
#print axioms step_setFieldAt_i32_4_eq
#print axioms step_setFieldAt_i64_eq
#print axioms step_fieldAt_aggregate_4_eq
#print axioms step_fieldAt_aggregate_8_eq
#print axioms step_ldfld_aggregate_value_eq
#print axioms step_ldfld_aggregate_snapshot_eq
#print axioms step_initobj_reference_eq

end CIL.Safety
