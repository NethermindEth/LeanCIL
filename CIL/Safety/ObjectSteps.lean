import CIL.Safety.StepComposition
import CIL.Safety.ObjectAllocationLemmas

/-!
# Object step equations

`cil_step` equations for the instructions that observe class instance references: identity
comparison (`ceq`, `beq`, `bne.un`), presence (`cgt.un` against null, `brtrue`, `brfalse`) and
`ldnull`, `ldfld`/`stfld` of scalar class fields, and `newobj` of a class, which calls the
constructor with a fresh instance that `allocateObject_ok` or `allocateObject_insufficient`
decides, and `callvirt` of a non-virtual method, which calls with a live receiver and throws
`NullReferenceException` on a null one (`receiverCall`). Each states the dispatcher arm of
`CIL/Safety/Execution.lean` for object operands, so stepping never unfolds the dispatcher. The
observations themselves unfold through `cil_checked` down to `formObject`, which a caller's
facts or `formObject_null` decide; field accesses leave `objectFieldAddress` and the byte
access for a caller's facts, one equation per field width.
-/

namespace CIL.Safety

/-- The null object reference forms in every memory. -/
@[cil_checked] theorem formObject_null (memory : Memory) :
    formObject memory .null = .ok (.object .null) := rfl

#print axioms formObject_null

attribute [cil_checked] objectNonNull objectEqual objectAboveNull

/-- A formed object reference is a checked value as it stands. -/
@[cil_checked] theorem checkedValue_object (memory : Memory) (reference : ManagedReference)
    (formed : formObject memory reference = .ok (.object reference)) :
    checkedValue memory (.object reference) = .ok (.object reference) := formed

#print axioms checkedValue_object

/-- An object home loads its formed reference. -/
@[cil_checked] theorem loadLocal_object (memory : Memory) (reference : ManagedReference)
    (formed : formObject memory reference = .ok (.object reference)) :
    loadLocal memory (.object (some reference)) = .ok (.object reference) := formed

#print axioms loadLocal_object

/-- Replacing an object home's reference preserves memory and requires the new one to form. -/
@[cil_checked] theorem storeLocal_object (memory : Memory) (previous : Option ManagedReference)
    (reference : ManagedReference)
    (formed : formObject memory reference = .ok (.object reference)) :
    storeLocal memory (.object previous) (.object reference) =
      .ok (.object (some reference), memory) := by
  simp [storeLocal, Value.hasUnspecified, formed, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms storeLocal_object

section ObjectEquations

variable (body : CIL.Method) (pc : Nat) (args : List Value) (frame : Frame) (memory : Memory)

/-- `newobj` of a class checks its `argc` arguments, allocates the instance and calls the
    constructor with it as the receiver; the instance waits under the rest of the stack. -/
@[cil_step] theorem step_newObject_eq (callee argc : Nat) (owner : CIL.Extraction.TypeExpr)
    (bases : List CIL.Extraction.TypeExpr) (size : Nat) (stack : List Value) :
    step body (.newObject callee argc owner bases size) pc args frame stack memory =
      if unspecifiedOperands argc stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else if stack.length < argc then .error .invalidState
      else do
        let arguments ← (stack.take argc).reverse.mapM (checkedValue memory)
        let (object, allocated) ← allocateObject memory ⟨owner, bases⟩ size
        return FrameAction.call callee (.object (.address object) :: arguments)
          (.object (.address object) :: stack.drop argc) allocated := by
  simp only [step, observerCount, Bool.or_false]

#print axioms step_newObject_eq

/-- The call a receiver-checked `callvirt` makes with checked `arguments`, receiver first: a null
    receiver throws `NullReferenceException`, and a receiver that is no object reference is
    ill-typed. This is the `callInstance` arm of `step` after its argument checks. -/
def receiverCall (callee : Nat) (arguments rest : List Value) (memory : Memory) :
    ExecutionResult FrameAction :=
  match arguments with
  | .object (.address _) :: _ => .ok (.call callee arguments rest memory)
  | .object .null :: _ => .error (.thrown "System.NullReferenceException")
  | _ => .error .invalidState

/-- `callvirt` of a non-virtual method checks its `argc` arguments and calls with a live receiver;
    a null receiver throws `NullReferenceException` before the call. -/
@[cil_step] theorem step_callInstance_eq (callee argc : Nat) (stack : List Value) :
    step body (.callInstance callee argc) pc args frame stack memory =
      if unspecifiedOperands argc stack then
        .error (.unsupported "Instruction observes unspecified vector bits")
      else if stack.length < argc then .error .invalidState
      else (do
        let arguments ← (stack.take argc).reverse.mapM (checkedValue memory)
        receiverCall callee arguments (stack.drop argc) memory) := by
  simp only [step, observerCount, Bool.or_false]
  rfl

#print axioms step_callInstance_eq

/-- A live receiver makes the call with the checked arguments as they stand. -/
@[cil_checked] theorem receiverCall_address (callee : Nat) (receiver : Reference)
    (arguments rest : List Value) :
    receiverCall callee (.object (.address receiver) :: arguments) rest memory =
      .ok (.call callee (.object (.address receiver) :: arguments) rest memory) := rfl

#print axioms receiverCall_address

/-- A null receiver throws before the call. -/
@[cil_checked] theorem receiverCall_null (callee : Nat) (arguments rest : List Value) :
    receiverCall callee (.object .null :: arguments) rest memory =
      .error (.thrown "System.NullReferenceException") := rfl

#print axioms receiverCall_null

/-- `ceq` on two object references pushes their identity comparison. -/
@[cil_step high] theorem step_eq_object_eq (left right : ManagedReference) (rest : List Value) :
    step body .eq pc args frame (.object right :: .object left :: rest) memory = do
      let equal ← objectEqual memory left right
      return .next (pc + 1) (.scalar (.i32 (if equal then 1 else 0)) :: rest) frame memory :=
  rfl

/-- `beq` on two object references branches when they are the same instance. -/
@[cil_step high] theorem step_beq_object_eq (target : Nat) (left right : ManagedReference)
    (rest : List Value) :
    step body (.beq target) pc args frame (.object right :: .object left :: rest) memory = do
      let equal ← objectEqual memory left right
      return .next (if equal then target else pc + 1) rest frame memory :=
  rfl

/-- `bne.un` on two object references branches when they are different instances. -/
@[cil_step high] theorem step_bne_object_eq (target : Nat) (left right : ManagedReference)
    (rest : List Value) :
    step body (.bne target) pc args frame (.object right :: .object left :: rest) memory = do
      let equal ← objectEqual memory left right
      return .next (if equal then pc + 1 else target) rest frame memory :=
  rfl

/-- `cgt.un` of an object reference against null pushes whether the reference is present. -/
@[cil_step high] theorem step_gtu_object_eq (left right : ManagedReference) (rest : List Value) :
    step body .gtu pc args frame (.object right :: .object left :: rest) memory = do
      let present ← objectAboveNull memory left right
      return .next (pc + 1) (.scalar (.i32 (if present then 1 else 0)) :: rest) frame memory :=
  rfl

/-- `brfalse` on an object reference branches when it is null. -/
@[cil_step high] theorem step_brzero_object_eq (target : Nat) (value : ManagedReference)
    (rest : List Value) :
    step body (.brzero target) pc args frame (.object value :: rest) memory = do
      let present ← objectNonNull memory value
      return .next (if present then pc + 1 else target) rest frame memory :=
  rfl

/-- `brtrue` on an object reference branches when it is present. -/
@[cil_step high] theorem step_brnonzero_object_eq (target : Nat) (value : ManagedReference)
    (rest : List Value) :
    step body (.brnonzero target) pc args frame (.object value :: rest) memory = do
      let present ← objectNonNull memory value
      return .next (if present then target else pc + 1) rest frame memory :=
  rfl

/-- `ldnull` pushes the null object reference and leaves memory unchanged. -/
@[cil_step high] theorem step_nullObject_eq (stack : List Value) :
    step body (.memory .nullObject) pc args frame stack memory =
      .ok (.next (pc + 1) (.object .null :: stack) frame memory) := by
  simp only [step, observerCount, Bool.or_false, staticInstruction, memoryInstruction,
    CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take, List.any]
  rfl

/-- `ldfld` of a scalar field of an object loads it from the field's located address. -/
theorem step_objectField_eq (owner : CIL.Extraction.TypeExpr)
    (offset width : Nat) (signed : Bool) (fits : width ∈ [1, 2, 4, 8])
    (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.objectField owner offset width signed)) pc args frame
        (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let value ← loadValue memory (.address address) width signed
      return .next (pc + 1) (.scalar value :: rest) frame memory := by
  simp only [step, observerCount, Bool.or_false, staticInstruction, memoryInstruction,
    objectFieldInstruction, CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take,
    List.any, fits, not_true_eq_false, ite_false, Value.hasUnspecified, Bool.false_eq_true,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases objectFieldAddress memory reference owner offset <;> try rfl
  rename_i address
  dsimp only
  cases loadValue memory (.address address) width signed <;> rfl

/-- `stfld` of a 64-bit object field writes the value's bytes at the located address. -/
@[cil_step high] theorem step_setObjectField_i64_eq (owner : CIL.Extraction.TypeExpr)
    (offset : Nat) (bits : BitVec 64) (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.setObjectField owner offset 8)) pc args frame
        (.scalar (.i64 bits) :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let after ← checkedAt (.address address) 8
        (write memory address (numberBytes bits.toNat 8) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame after := by
  simp only [step, observerCount, Bool.or_false, staticInstruction, memoryInstruction,
    objectFieldInstruction, CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take,
    List.any, Value.hasUnspecified, CIL.Value.hasUnspecified, Bool.false_eq_true, ite_false,
    Bind.bind, Except.bind, Pure.pure, Except.pure]
  cases objectFieldAddress memory reference owner offset <;> try rfl
  rename_i address
  dsimp only
  cases checkedAt (.address address) 8
    (write memory address (numberBytes bits.toNat 8) ordinaryAccessAlignment) <;> rfl

/-- `stfld` of a 1-, 2- or 4-byte object field writes the low bytes of the int32 value. -/
theorem step_setObjectField_i32_eq (owner : CIL.Extraction.TypeExpr)
    (offset width : Nat) (narrow : width ∈ [1, 2, 4]) (bits : BitVec 32)
    (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.setObjectField owner offset width)) pc args frame
        (.scalar (.i32 bits) :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let after ← checkedAt (.address address) width
        (write memory address (numberBytes bits.toNat width) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame after := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at narrow
  rcases narrow with rfl | rfl | rfl
  all_goals
    simp only [step, observerCount, Bool.or_false, staticInstruction, memoryInstruction,
      objectFieldInstruction, CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take,
      List.any, Value.hasUnspecified, CIL.Value.hasUnspecified, Bool.false_eq_true,
      ite_false, Bind.bind, Except.bind, Pure.pure, Except.pure]
    cases objectFieldAddress memory reference owner offset <;> try rfl
    rename_i address
    dsimp only
    cases checkedAt (.address address) _
      (write memory address (numberBytes bits.toNat _) ordinaryAccessAlignment) <;> rfl


/-- `ldfld` of a class-typed object field pushes the reference its located slot holds. -/
@[cil_step high] theorem step_objectReferenceField_eq (owner : CIL.Extraction.TypeExpr)
    (offset : Nat) (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.objectReferenceField owner offset)) pc args frame
        (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let value ← loadSlot memory address
      return .next (pc + 1) (value :: rest) frame memory := by
  simp only [step, observerCount, Bool.or_false, staticInstruction, memoryInstruction,
    objectFieldInstruction, CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take,
    List.any, Value.hasUnspecified, Bool.false_eq_true, ite_false, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  cases objectFieldAddress memory reference owner offset <;> try rfl
  rename_i address
  dsimp only
  cases loadSlot memory address <;> rfl

/-- `stfld` of a class-typed object field stores the reference into its located slot. -/
@[cil_step high] theorem step_setObjectReferenceField_eq (owner : CIL.Extraction.TypeExpr)
    (offset : Nat) (value reference : ManagedReference) (rest : List Value) :
    step body (.memory (.setObjectReferenceField owner offset)) pc args frame
        (.object value :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let after ← storeSlot memory address value
      return .next (pc + 1) rest frame after := by
  simp only [step, observerCount, Bool.or_false, staticInstruction, memoryInstruction,
    objectFieldInstruction, CIL.MemoryOp.argumentCount, unspecifiedOperands, List.take,
    List.any, Value.hasUnspecified, Bool.false_eq_true, ite_false, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  cases objectFieldAddress memory reference owner offset <;> try rfl
  rename_i address
  dsimp only
  cases storeSlot memory address value <;> rfl

/-- A readable slot loads the reference it holds, which must still form. -/
theorem loadSlot_of_access {memory : Memory} {field : Reference}
    (readable : access memory field objectFieldSlot ordinaryAccessAlignment false = .ok ()) :
    loadSlot memory field = formObject memory (memory.slots field.allocation field.offset) := by
  simp only [loadSlot, readable, checkedAt, Except.mapError, Bind.bind, Except.bind]

/-- A writable slot stores a formed reference, changing nothing else. -/
theorem storeSlot_of_access {memory : Memory} {field : Reference} {value : ManagedReference}
    (writable : access memory field objectFieldSlot ordinaryAccessAlignment true = .ok ())
    (formed : formObject memory value = .ok (.object value)) :
    storeSlot memory field value = .ok (setSlot memory field value) := by
  simp only [storeSlot, writable, formed, checkedAt, Except.mapError, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

/-- `ldfld` of a 1-byte object field, as `step_objectField_eq` states it. -/
@[cil_step high] theorem step_objectField_1_eq (owner : CIL.Extraction.TypeExpr)
    (offset : Nat) (signed : Bool) (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.objectField owner offset 1 signed)) pc args frame
        (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let value ← loadValue memory (.address address) 1 signed
      return .next (pc + 1) (.scalar value :: rest) frame memory :=
  by apply step_objectField_eq; decide

/-- `ldfld` of a 2-byte object field, as `step_objectField_eq` states it. -/
@[cil_step high] theorem step_objectField_2_eq (owner : CIL.Extraction.TypeExpr)
    (offset : Nat) (signed : Bool) (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.objectField owner offset 2 signed)) pc args frame
        (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let value ← loadValue memory (.address address) 2 signed
      return .next (pc + 1) (.scalar value :: rest) frame memory :=
  by apply step_objectField_eq; decide

/-- `ldfld` of a 4-byte object field, as `step_objectField_eq` states it. -/
@[cil_step high] theorem step_objectField_4_eq (owner : CIL.Extraction.TypeExpr)
    (offset : Nat) (signed : Bool) (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.objectField owner offset 4 signed)) pc args frame
        (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let value ← loadValue memory (.address address) 4 signed
      return .next (pc + 1) (.scalar value :: rest) frame memory :=
  by apply step_objectField_eq; decide

/-- `ldfld` of a 8-byte object field, as `step_objectField_eq` states it. -/
@[cil_step high] theorem step_objectField_8_eq (owner : CIL.Extraction.TypeExpr)
    (offset : Nat) (signed : Bool) (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.objectField owner offset 8 signed)) pc args frame
        (.object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let value ← loadValue memory (.address address) 8 signed
      return .next (pc + 1) (.scalar value :: rest) frame memory :=
  by apply step_objectField_eq; decide

/-- `stfld` of a 1-byte object field, as `step_setObjectField_i32_eq` states it. -/
@[cil_step high] theorem step_setObjectField_i32_1_eq (owner : CIL.Extraction.TypeExpr)
    (offset : Nat) (bits : BitVec 32) (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.setObjectField owner offset 1)) pc args frame
        (.scalar (.i32 bits) :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let after ← checkedAt (.address address) 1
        (write memory address (numberBytes bits.toNat 1) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame after :=
  by apply step_setObjectField_i32_eq; decide

/-- `stfld` of a 2-byte object field, as `step_setObjectField_i32_eq` states it. -/
@[cil_step high] theorem step_setObjectField_i32_2_eq (owner : CIL.Extraction.TypeExpr)
    (offset : Nat) (bits : BitVec 32) (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.setObjectField owner offset 2)) pc args frame
        (.scalar (.i32 bits) :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let after ← checkedAt (.address address) 2
        (write memory address (numberBytes bits.toNat 2) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame after :=
  by apply step_setObjectField_i32_eq; decide

/-- `stfld` of a 4-byte object field, as `step_setObjectField_i32_eq` states it. -/
@[cil_step high] theorem step_setObjectField_i32_4_eq (owner : CIL.Extraction.TypeExpr)
    (offset : Nat) (bits : BitVec 32) (reference : ManagedReference) (rest : List Value) :
    step body (.memory (.setObjectField owner offset 4)) pc args frame
        (.scalar (.i32 bits) :: .object reference :: rest) memory = do
      let address ← objectFieldAddress memory reference owner offset
      let after ← checkedAt (.address address) 4
        (write memory address (numberBytes bits.toNat 4) ordinaryAccessAlignment)
      return .next (pc + 1) rest frame after :=
  by apply step_setObjectField_i32_eq; decide

end ObjectEquations

#print axioms step_eq_object_eq
#print axioms step_beq_object_eq
#print axioms step_bne_object_eq
#print axioms step_gtu_object_eq
#print axioms step_brzero_object_eq
#print axioms step_brnonzero_object_eq
#print axioms step_nullObject_eq
#print axioms step_objectField_eq
#print axioms step_setObjectField_i64_eq
#print axioms step_setObjectField_i32_eq
#print axioms step_objectField_1_eq
#print axioms step_objectField_2_eq
#print axioms step_objectField_4_eq
#print axioms step_objectField_8_eq
#print axioms step_setObjectField_i32_1_eq
#print axioms step_setObjectField_i32_2_eq
#print axioms step_setObjectField_i32_4_eq
#print axioms step_objectReferenceField_eq
#print axioms step_setObjectReferenceField_eq
#print axioms loadSlot_of_access
#print axioms storeSlot_of_access

end CIL.Safety
