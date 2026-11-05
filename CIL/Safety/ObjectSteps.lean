import CIL.Safety.StepComposition

/-!
# Object step equations

`cil_step` equations for the instructions that observe class instance references: identity
comparison (`ceq`, `beq`, `bne.un`), presence (`cgt.un` against null, `brtrue`, `brfalse`) and
`ldnull`. Each states the dispatcher arm of `CIL/Safety/Execution.lean` for object operands,
so stepping never unfolds the dispatcher. The observations themselves unfold through
`cil_checked` down to `formObject`, which a caller's facts or `formObject_null` decide.
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

end ObjectEquations

#print axioms step_eq_object_eq
#print axioms step_beq_object_eq
#print axioms step_bne_object_eq
#print axioms step_gtu_object_eq
#print axioms step_brzero_object_eq
#print axioms step_brnonzero_object_eq
#print axioms step_nullObject_eq

end CIL.Safety
