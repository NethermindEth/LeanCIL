import Extracted
import CIL.Safety.SymbolicExecution

/-!
# String values

`Examples.Strings.Pick(first, left, right)` returns `left` when `first` holds and `right`
otherwise, through a string local. A string is an opaque object reference: it is passed,
stored and returned, and nothing reads its characters. Proved: the result is exactly the
argument chosen, null or not, with memory unchanged.
-/

open CIL
namespace ExampleProof

/-- `Pick` returns the reference it selects, unchanged, for any pair of strings that form. -/
theorem correctness (memory : CIL.Safety.Memory) (first : Bool)
    (left right : CIL.Safety.ManagedReference)
    (leftFormed : CIL.Safety.formObject memory left = .ok (.object left))
    (rightFormed : CIL.Safety.formObject memory right = .ok (.object right)) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0
        [.scalar (.i32 (if first then 1 else 0)), .object left, .object right] memory =
      .ok (memory, [.object (if first then left else right)]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cases first <;> cil_checked_steps [leftFormed, rightFormed, CIL.Safety.leaveFrame]

#print axioms correctness
end ExampleProof
