import CIL.Safety.InstructionReferences
import CIL.Safety.StaticInitialization

/-!
# Static references are valid

A loaded readonly static binding is a reference that forms in memory, and a static memory
instruction run by the checked interpreter (`CIL/Safety/Execution.lean`) leaves only valid
values on the stack. Contracts use these to keep `ValuesValid` across static loads.
-/

namespace CIL.Safety

theorem StaticBindingValid.reference_valid {m : Memory} {descriptor : CIL.StaticDescriptor}
    {reference : Reference} (valid : StaticBindingValid m descriptor reference) :
    form m reference = .ok reference := by
  obtain ⟨_, _, _, _, _, _, _, bytes⟩ := valid
  exact read_reference_valid _ _ _ _ _ bytes

/-- A successful static memory instruction pushes only values valid in the resulting memory. -/
theorem staticInstruction_values_valid (body : CIL.Method) (pc : Nat) (operation : CIL.MemoryOp)
    (stack values : List Value) (m result : Memory) (hm : m.WellFormed)
    (valid : ValuesValid m stack)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    ValuesValid result values :=
  (staticInstruction_contract _ _ _ _ _ _ _ h).values hm valid

#print axioms access_reference_valid
#print axioms staticReference_reference_valid
#print axioms staticInstruction_values_valid

end CIL.Safety
