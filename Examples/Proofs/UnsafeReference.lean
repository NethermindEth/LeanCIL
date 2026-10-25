import Extracted
import Examples.Support
import CIL.Safety.SymbolicExecution

namespace ExampleProof
open CIL.Safety

/-- Reinterpreting a live reference preserves the complete memory, including
    initialization flags, access views, allocation identities and lifetimes. -/
theorem reinterpret_preserves (memory : Memory) (reference : Reference) (rest : List Value)
    (formed : form memory reference = .ok reference) :
    memoryInstruction .asRef (.reference (.address reference) :: rest) memory =
      .ok (memory, .reference (.address reference) :: rest) := by
  simp [memoryInstruction, CIL.MemoryOp.argumentCount, unspecifiedOperands,
    CIL.Safety.Value.hasUnspecified, formValue, checkedAt, formed, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The compiled cast preserves arbitrary caller memory and the precise reference. -/
theorem correctness (memory : Memory) (reference : Reference)
    (formed : form memory reference = .ok reference) :
    invoke Extracted.program 4 0 [.reference (.address reference)] memory =
      .ok (memory, [.reference (.address reference)]) := by
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, formed, instruction, staticInstruction, memoryInstruction,
    observerCount, CIL.MemoryOp.argumentCount, unspecifiedOperands, CIL.Safety.Value.hasUnspecified,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  all_goals simp [run, Extracted.program, Extracted.method0, step, checkedValue, formValue,
    observerCount, CIL.MemoryOp.argumentCount, unspecifiedOperands, CIL.Safety.Value.hasUnspecified,
    checkedAt, formed, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

#print axioms reinterpret_preserves
#print axioms correctness

end ExampleProof
