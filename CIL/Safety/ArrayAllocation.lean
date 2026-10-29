import CIL.Safety.InstructionMemory

/-!
# Reference-free heap arrays

Array allocation reuses fresh allocation identities and existing typed array views, enforcing
the .NET 10 element-count ceiling. Success still assumes runtime allocation availability;
the model does not certify heap capacity or GC behavior. Unsupported extents remain model faults.
Composite payloads retain the runtime's eight-byte base alignment independently of element stride.
-/

namespace CIL.Safety

/-- The .NET 10 CoreCLR single-dimensional array element-count ceiling. -/
def maxArrayLength : Nat := 0x7fffffc7

/-- Initialize only the fresh payload and grant its complete read/write view. -/
def arrayMemory (allocated : Memory) (identity size : Nat) : Memory :=
  { allocated with
    cells := fun other offset =>
      if other == identity then ⟨0, true⟩ else allocated.cells other offset
    views := ⟨identity, 0, size, true, true⟩ :: allocated.views }

/-- A fresh zero-initialized array with byte authority over exactly its payload.
    Initialization uses a constant cell function, independent of the requested length. -/
def allocateArray (memory : Memory) (element : CIL.ArrayElement) (length : Nat) :
    ExecutionResult (ArrayView × Memory) := do
  if !element.allocationSupported then
    .error (.unsupported "Unsupported array element allocation") else pure ()
  if length > maxArrayLength then
    .error (.unsupported "Array length outside supported extent") else pure ()
  let size := length * element.width
  let (identity, allocated) ← checkedAt .null size
    (allocate memory ⟨.managedHeap, ⟨size, element.allocationAlignment, []⟩, true, [size]⟩)
  return (⟨.address ⟨identity, 0⟩, length, element⟩, arrayMemory allocated identity size)

/-- Decode the CLI signed int32/native length before allocating; negative lengths overflow. -/
def newArray (memory : Memory) (element : CIL.ArrayElement) (value : CIL.Value) :
    ExecutionResult (ArrayView × Memory) := do
  if !element.allocationSupported then
    .error (.unsupported "Unsupported array element allocation") else pure ()
  let length ← match value with
    | .i32 bits => pure bits.toInt
    | .i64 bits => pure bits.toInt
    | _ => .error .invalidState
  if length < 0 then .error (.thrown "System.OverflowException") else
    allocateArray memory element length.toNat

end CIL.Safety
