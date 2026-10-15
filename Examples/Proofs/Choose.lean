import Extracted
import CIL.Safety.SymbolicExecution

open CIL
namespace ExampleProof

/-- Both canonical Boolean inputs choose the requested value and preserve every caller memory. -/
theorem correctness (memory : CIL.Safety.Memory) (flag : Bool) (x y : W64) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0
      [.scalar (.i32 (if flag then 1 else 0)), .scalar (.i64 x), .scalar (.i64 y)] memory =
      .ok (memory, [.scalar (.i64 (if flag then x else y))]) := by
  cases flag <;> refine ⟨CIL.executionBound Extracted.program 0, ?_⟩ <;>
    cil_checked_steps [CIL.truth, CIL.NarrowKind.extend]

#print axioms correctness
end ExampleProof
