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
  simp [memoryInstruction, formValue, checkedAt, formed, Except.mapError,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The compiled cast preserves arbitrary caller memory and the precise reference. -/
theorem correctness (memory : Memory) (reference : Reference)
    (formed : form memory reference = .ok reference) :
    invoke Extracted.program 4 0 [.reference (.address reference)] memory =
      .ok (memory, [.reference (.address reference)]) := by
  cil_checked_steps [checkedValue, numericValue, formValue, checkedAt, formed, instruction, staticInstruction, memoryInstruction,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  simp [run, Extracted.program, Extracted.method0, step, checkedValue, formValue,
    checkedAt, formed, leaveFrame, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

end ExampleProof
