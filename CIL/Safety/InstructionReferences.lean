import CIL.Safety.LiveValues

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
