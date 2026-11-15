import CIL.Safety.StepFlow

/-! The pc a step resumes at and the action shape it produces, read off the instruction alone. -/
namespace Tests.StepFlow

open CIL (Method Instruction)
open CIL.Safety

variable {body : Method} {pc : Nat} {args stack stack' : List Value} {frame frame' : Frame} {m m' : Memory}
  {target : Nat}

example (h : step body (.bge 7) pc args frame stack m = .ok (.next target stack' frame' m')) :
    target = pc + 1 ∨ target = 7 := by
  simpa [Instruction.continues, Instruction.targets] using step_next_target h

/-- An unconditional branch does not continue, so it can only resume at its target. -/
example (h : step body (.br 9) pc args frame stack m = .ok (.next target stack' frame' m')) : target = 9 := by
  simpa [Instruction.continues, Instruction.targets] using step_next_target h

/-- An out-of-range switch index falls through, so the fallthrough stays possible. -/
example (h : step body (.switch [3, 5]) pc args frame stack m = .ok (.next target stack' frame' m')) :
    target = pc + 1 ∨ target = 3 ∨ target = 5 := by
  simpa [Instruction.continues, Instruction.targets] using step_next_target h

example (h : step body (.blt 4) pc args frame stack m = .ok (.next target stack' frame' m')) :
    target = pc + 1 ∨ target = 4 := by
  simpa [Instruction.continues, Instruction.targets] using step_next_target h

/-- A return never resumes in the frame. -/
example : step body (.ret) pc args frame stack m ≠ .ok (.next target stack' frame' m') :=
  fun h => by
  simpa [Instruction.continues, Instruction.targets] using step_next_target h

/-- Both branch outcomes occur, so the disjunction above is not vacuous. -/
example : step body (.bge 7) 3 args frame [.scalar (.i32 0), .scalar (.i32 1)] m = .ok (.next 7 [] frame m) := by
  rfl
example : step body (.bge 7) 3 args frame [.scalar (.i32 1), .scalar (.i32 0)] m = .ok (.next 4 [] frame m) := by
  rfl

example {r : Reference} (h : step body (.call 2 1) pc args frame stack m = .ok (.construct 2 args stack frame' r .word64 m')) :
    False := by
  obtain ⟨_, _, _, _, _, contradiction⟩ := step_call_action h
  cases contradiction

example {argc size}
    (h : step body (.newAggregate 2 argc size) pc args frame stack m =
      .ok (.call 2 args stack m')) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, contradiction⟩ := step_newAggregate_action h
  cases contradiction

/-- A call whose operand names method 1 at a pc whose link names method 2. -/
def relinked : Method :=
  { code := [.call 1 0, .ret], locals := [], returnsValue := false, links := [(0, .direct 2)] }

/-- The call enters the method its link names, not the one its operand names. -/
theorem relinked_call : step relinked (.call 1 0) 0 args frame [] m = .ok (.call 2 [] [] m) := rfl

/-- A call site the table gives no link faults instead of entering its operand. -/
theorem unlinked_call :
    step { relinked with links := [] } (.call 1 0) 0 args frame [] m = .error unlinkedCall := rfl

#print axioms relinked_call
#print axioms unlinked_call
#print axioms step_next_target
#print axioms step_call_action
#print axioms step_newAggregate_action
#print axioms step_callee

end Tests.StepFlow
