import Extracted
import Examples.Support

namespace ExampleProof
open CIL.Safety

def uninitialized : Memory := { Examples.caller with
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨32, 1, []⟩, true, [32]⟩ else none
  cells := fun _ _ => ⟨37, false⟩
  views := [⟨0, 0, 32, true, true⟩] }

-- The compiled call consumes its reference without changing any caller byte,
-- including initialization flags. It does not initialize an out parameter.
theorem correctness :
    invoke Extracted.program 4 0 [Examples.reference] uninitialized = .ok (uninitialized, []) := by
  rfl

theorem instruction_preserves (memory : Memory) (reference : ManagedReference) (stack : List Value)
    (valid : ∃ value, formValue memory reference = .ok value) :
    instruction .skipInit (.reference reference :: stack) memory = .ok (memory, stack) := by
  obtain ⟨value, valid⟩ := valid
  simp [instruction, valid, Functor.map, Except.map]

end ExampleProof
