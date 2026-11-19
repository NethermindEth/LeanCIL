import CIL.Safety.Execution

/-! Execution of the reference subtraction model on the native offset operands of Unsafe. -/

namespace Tests.UnsafeOffsets
open CIL CIL.Safety

/-- Signed and unsigned native offsets both arrive as 64-bit words. The model and CIL sub
    move the same reference and preserve its readonly restriction for every word. -/
theorem subtractByteOffset_step (body : Method)
    (pc : Nat) (args : List Safety.Value) (frame : Frame) (rest : List Safety.Value)
    (memory : Safety.Memory) (base : ManagedReference) (offset : W64) (readOnly : Bool) :
    let reference := if readOnly then Safety.Value.readOnlyReference base else .reference base
    let stack := .scalar (.i64 offset) :: reference :: rest
    modelStep (some .referenceSubtract) body pc frame stack memory =
      step body .sub pc args frame stack memory := by
  cases readOnly <;> rfl

#print axioms subtractByteOffset_step

end Tests.UnsafeOffsets
