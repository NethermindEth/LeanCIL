import Extracted
import CIL.Safety.SymbolicExecution

/-! Checked reference reinterpretation preserves the address and all caller memory. -/

namespace ExampleProof
open CIL.Safety

/-- Reinterpreting a live reference preserves the complete memory, including
    initialization flags, access views, allocation identities and lifetimes. -/
theorem reinterpret_preserves (body : CIL.Method) (pc : Nat) (args : List Value)
    (frame : Frame) (memory : Memory) (reference : Reference) (rest : List Value)
    (formed : form memory reference = .ok reference) :
    step body (.memory .asRef) pc args frame (.reference (.address reference) :: rest) memory =
      .ok (.next (pc + 1) (.reference (.address reference) :: rest) frame memory) := by
  cil_checked_step [formed]

/-- The compiled cast preserves arbitrary caller memory and the precise reference. -/
theorem correctness (memory : Memory) (reference : Reference)
    (formed : form memory reference = .ok reference) :
    invoke Extracted.program 4 0 [.reference (.address reference)] memory =
      .ok (memory, [.reference (.address reference)]) := by
  cil_checked_steps [formed]

#print axioms reinterpret_preserves
#print axioms correctness

end ExampleProof
