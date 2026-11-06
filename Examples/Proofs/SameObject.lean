import Extracted
import CIL.Safety.SymbolicExecution

open CIL
namespace ExampleProof

/-- `left == right` on class instances is reference identity: it is true exactly when both
    arguments name the same allocation or are both null, and it leaves memory unchanged. -/
theorem correctness (memory : CIL.Safety.Memory) (left right : CIL.Safety.ManagedReference)
    (leftFormed : CIL.Safety.formObject memory left = .ok (.object left))
    (rightFormed : CIL.Safety.formObject memory right = .ok (.object right)) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object left, .object right] memory =
      .ok (memory, [.scalar (.i32 (if left = right then 1 else 0))]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [leftFormed, rightFormed]

#print axioms correctness
end ExampleProof
