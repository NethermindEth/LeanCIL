import CIL.Safety.StepFlow
import Tests.Support

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

example {r : Reference}
    (h : step body (.call (Tests.callee 1)) pc args frame stack m =
      .ok (.construct 2 args stack frame' r .word64 m')) :
    False := by
  rcases step_call_action h with ⟨_, _, plain⟩ | ⟨_, _, _, _, _, contradiction, _⟩
  · rw [if_neg (by decide)] at plain
    obtain ⟨_, _, _, contradiction⟩ := plain
    cases contradiction
  · cases contradiction

example {constructor : CIL.Extraction.MethodRef} {size}
    (linked : body.linkAt pc = some (.aggregate 2 size))
    (h : step body (.newobj constructor) pc args frame stack m =
      .ok (.call 2 args stack m')) :
    False := by
  obtain ⟨_, _, _, _, _, _, contradiction⟩ := step_newobj_aggregate_action linked h
  cases contradiction

/-- A parameterless call at a pc whose link names method 2. -/
def relinked : Method :=
  { code := [.call (Tests.callee 0) {}, .ret], locals := [], returnsValue := false,
    links := [(0, .direct 2)] }

/-- The call enters the method its link names. -/
theorem relinked_call :
    step relinked (.call (Tests.callee 0)) 0 args frame [] m = .ok (.call 2 [] [] m) := rfl

/-- A call site the table gives no link faults instead of entering any method. -/
theorem unlinked_call :
    step { relinked with links := [] } (.call (Tests.callee 0)) 0 args frame [] m =
      .error unlinkedCall := rfl

/-- A tail call the table gives no link faults before its stack check, which an empty stack under
    one argument would fail with `invalidState`. -/
theorem unlinked_tail_call :
    step {
        code := [.call (Tests.callee 1) { tail := true }], locals := [], returnsValue := false,
        links := [] }
      (.call (Tests.callee 1) { tail := true }) 0 args frame [] m = .error unlinkedCall := rfl

/-- A construction the table gives no link faults before its size check, which size 0 would fail
    with `invalidState`. -/
theorem unlinked_aggregate :
    step { code := [.newobj (.arity 0)], locals := [], returnsValue := true, links := [] }
      (.newobj (.arity 0)) 0 args frame [] m = .error unlinkedCall := rfl

/-- A construction under a link of a call kind faults; only a constructor link allocates. -/
theorem miskinded_construction :
    step { code := [.newobj (.arity 0)], locals := [], returnsValue := true,
           links := [(0, .direct 1)] }
      (.newobj (.arity 0)) 0 args frame [] m = .error unlinkedCall := rfl

#print axioms relinked_call
#print axioms unlinked_call
#print axioms unlinked_tail_call
#print axioms unlinked_aggregate
#print axioms miskinded_construction
#print axioms step_next_target
#print axioms step_call_action
#print axioms step_newobj_aggregate_action
#print axioms step_callee

end Tests.StepFlow
