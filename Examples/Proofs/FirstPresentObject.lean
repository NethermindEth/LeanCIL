import Extracted
import CIL.Safety.SymbolicExecution

open CIL
namespace ExampleProof

/-- An object local carries a reference through a branch on presence and returns it
    unchanged: the first argument when present, otherwise the second. -/
theorem correctness (memory : CIL.Safety.Memory) (first second : CIL.Safety.ManagedReference)
    (firstFormed : CIL.Safety.formObject memory first = .ok (.object first))
    (secondFormed : CIL.Safety.formObject memory second = .ok (.object second)) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object first, .object second] memory =
      .ok (memory, [.object (if first = .null then second else first)]) := by
  by_cases absent : first = .null <;> cil_checked_steps [firstFormed, secondFormed, absent]

#print axioms correctness
end ExampleProof
