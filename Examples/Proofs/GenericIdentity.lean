import Extracted
import CIL.Safety.SymbolicExecution

namespace ExampleProof

/-- The compiled generic specialization and its caller return every input unchanged,
    preserving the entire caller memory. -/
theorem correctness (memory : CIL.Safety.Memory) (x : CIL.W64) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.scalar (.i64 x)] memory =
      .ok (memory, [.scalar (.i64 x)]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps

#print axioms correctness
end ExampleProof
