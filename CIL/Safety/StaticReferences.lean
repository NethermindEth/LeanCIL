import CIL.Safety.InstructionReferences
import CIL.Safety.StaticInitialization

namespace CIL.Safety

theorem StaticBindingValid.reference_valid {m : Memory} {descriptor : CIL.StaticDescriptor}
    {reference : Reference} (valid : StaticBindingValid m descriptor reference) :
    form m reference = .ok reference := by
  obtain ⟨_, _, _, _, _, _, bytes⟩ := valid
  exact read_reference_valid _ _ _ _ _ bytes

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
