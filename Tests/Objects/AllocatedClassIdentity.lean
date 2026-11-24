import Extracted
import CIL.Safety.Execution

/-! Constructors for two equally spelled classes allocate instances of distinct runtime types. -/

namespace ExampleProof
open CIL CIL.Safety

/-- The entry creates both objects, runs the same classifier on each, and returns 2 × 10 + 1. -/
theorem correctness :
    (invoke Extracted.program 64 0 [] Safety.Memory.empty).map Prod.snd =
      .ok [.scalar (.i32 21)] := by
  cil_kernel_rfl
#print axioms correctness

end ExampleProof
