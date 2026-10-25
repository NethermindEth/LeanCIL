import CIL.Safety.InstructionMemory

/-! # Checked reference observations

Null tests and equality inspect live allocation-relative references without reading storage
or granting access. Cross-allocation end pointers are rejected because allocation identities
alone do not determine whether their runtime addresses coincide.
-/

namespace CIL.Safety

/-- Extract a reference without changing the capability of the original stack value. -/
def Value.referenceValue : Value → Option ManagedReference
  | .reference value | .readOnlyReference value => some value
  | _ => none

/-- A null test validates a non-null reference but requires no byte access authority. -/
def referenceNonNull (memory : Memory) (reference : ManagedReference) : ExecutionResult Bool := do
  let _ ← formValue memory reference
  return match reference with | .null => false | .address _ => true

/-- Equality is exact within one allocation and between interiors of distinct allocations.
    Comparing an end pointer across allocations requires runtime address evidence we lack. -/
def referenceEqual (memory : Memory) (left right : ManagedReference) : ExecutionResult Bool := do
  let _ ← formValue memory left
  let _ ← formValue memory right
  match left, right with
  | .null, .null => return true
  | .null, .address _ | .address _, .null => return false
  | .address first, .address second =>
    if first.allocation == second.allocation then return first.offset == second.offset
    let firstAllocation ← checkedAt left 0 (liveAllocation memory first.allocation)
    let secondAllocation ← checkedAt right 0 (liveAllocation memory second.allocation)
    if first.offset < firstAllocation.layout.size &&
        second.offset < secondAllocation.layout.size then return false
    else .error (.unsupported "Cross-allocation end-pointer comparison")

/-- Two non-null, live references to one allocation, checked without byte access authority. -/
def referencePositions (memory : Memory) (left right : ManagedReference) :
    ExecutionResult (Nat × Nat) := do
  let first ← referenceAt left
  let second ← referenceAt right
  let _ ← checkedAt left 0 (form memory first)
  let _ ← checkedAt right 0 (form memory second)
  if first.allocation != second.allocation then
    .error (.unsupported "Cross-allocation pointer arithmetic")
  else return (first.offset, second.offset)

/-- Pointer differences return the native-width signed byte displacement, with modular bits. -/
def referenceDifference (memory : Memory) (left right : ManagedReference) :
    ExecutionResult CIL.W64 := do
  let (first, second) ← referencePositions memory left right
  return BitVec.ofNat 64 first - BitVec.ofNat 64 second

/-- Unsigned address ordering within one allocation agrees with ordering its offsets. -/
def referenceLess (memory : Memory) (left right : ManagedReference) : ExecutionResult Bool := do
  let (first, second) ← referencePositions memory left right
  return first < second

/-- Subtracting a signed byte offset retains provenance and checks the resulting position. -/
def referenceSubtract (memory : Memory) (reference : ManagedReference) (offset : CIL.Value) :
    ExecutionResult ManagedReference := do
  let some displacement := CIL.offsetValue true offset | .error .invalidState
  let address ← referenceAt reference
  let result ← checkedAt reference 0 (add memory address 1 (BitVec.ofInt 64 (-displacement)))
  return .address result
end CIL.Safety
