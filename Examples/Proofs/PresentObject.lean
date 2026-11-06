import Extracted
import CIL.Safety.SymbolicExecution

open CIL
namespace ExampleProof

/-- `account is not null` compiles to `cgt.un` against `ldnull`, which tests presence. -/
theorem correctness (memory : CIL.Safety.Memory) (account : CIL.Safety.ManagedReference)
    (formed : CIL.Safety.formObject memory account = .ok (.object account)) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object account] memory =
      .ok (memory, [.scalar (.i32 (if account = .null then 0 else 1))]) := by
  refine ⟨CIL.executionBound Extracted.program 0, ?_⟩
  cil_checked_steps [formed]
  split <;> rfl

#print axioms correctness
end ExampleProof
