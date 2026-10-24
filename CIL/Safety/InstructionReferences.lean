import CIL.Safety.LiveValues

/-!
# Instructions produce valid values

Corollaries of the instruction contracts: a successful memory or value instruction on a
stack of valid values in well-formed memory leaves only values valid in the result memory.
-/

namespace CIL.Safety

theorem memoryInstruction_values_valid (operation : CIL.MemoryOp) (stack values : List Value)
    (m result : Memory) (hm : m.WellFormed) (valid : ValuesValid m stack)
    (h : memoryInstruction operation stack m = .ok (result, values)) : ValuesValid result values :=
  (memoryInstruction_contract _ _ _ _ _ h).values hm valid

theorem instruction_values_valid (operation : CIL.Op) (stack values : List Value)
    (m result : Memory) (hm : m.WellFormed) (valid : ValuesValid m stack)
    (h : instruction operation stack m = .ok (result, values)) : ValuesValid result values :=
  (instruction_contract _ _ _ _ _ h).values hm valid

#print axioms memoryInstruction_values_valid
#print axioms instruction_values_valid

end CIL.Safety
