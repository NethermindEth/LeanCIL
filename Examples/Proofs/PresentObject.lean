import Extracted
import CIL.Safety.SymbolicExecution

open CIL
namespace ExampleProof

/-- `account is not null` compiles to `cgt.un` against `ldnull`, which tests presence. -/
theorem correctness (memory : CIL.Safety.Memory) (account : CIL.Safety.ManagedReference)
    (formed : CIL.Safety.formObject memory account = .ok (.object account)) :
    ∃ fuel, CIL.Safety.invoke Extracted.program fuel 0 [.object account] memory =
      .ok (memory, [.scalar (.i32 (if account = .null then 0 else 1))]) := by
  cil_checked_steps [formed]

#print axioms correctness
end ExampleProof
