import Extracted
import CIL.Safety.SymbolicExecution

open CIL
namespace ExampleProof

/-- `account is null` compares against the one null object reference that `ldnull` pushes. -/
theorem correctness (memory : CIL.Safety.Memory) (account : CIL.Safety.ManagedReference)
    (formed : CIL.Safety.formObject memory account = .ok (.object account)) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object account] memory =
      .ok (memory, [.scalar (.i32 (if account = .null then 1 else 0))]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [formed]

#print axioms correctness
end ExampleProof
