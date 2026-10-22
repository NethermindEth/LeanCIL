import CIL.Safety.StepFlow

/-! The pc a step resumes at and the action shape it produces, read off the instruction alone. -/
namespace Tests.StepFlow

open CIL (Method Op)
open CIL.Safety

variable {body : Method} {pc : Nat} {args stack stack' : List Value} {frame frame' : Frame} {m m' : Memory}
  {target : Nat}

example (h : step body (.bge 7) pc args frame stack m = .ok (.next target stack' frame' m')) :
    target = pc + 1 ∨ target = 7 := by
  simpa [Op.continues, Op.targets] using step_next_target h

/-- An unconditional branch does not continue, so it can only resume at its target. -/
example (h : step body (.branch 9) pc args frame stack m = .ok (.next target stack' frame' m')) : target = 9 := by
  simpa [Op.continues, Op.targets] using step_next_target h

/-- An out-of-range switch index falls through, so the fallthrough stays possible. -/
example (h : step body (.switch [3, 5]) pc args frame stack m = .ok (.next target stack' frame' m')) :
    target = pc + 1 ∨ target = 3 ∨ target = 5 := by
  simpa [Op.continues, Op.targets] using step_next_target h

example (h : step body (.nativeBinary (.blt 4)) pc args frame stack m = .ok (.next target stack' frame' m')) :
    target = pc + 1 ∨ target = 4 := by
  simpa [Op.continues, Op.targets] using step_next_target h

/-- A return never resumes in the frame. -/
example : step body (.ret none) pc args frame stack m ≠ .ok (.next target stack' frame' m') := fun h => by
  simpa [Op.continues, Op.targets] using step_next_target h

/-- Both branch outcomes occur, so the disjunction above is not vacuous. -/
example : step body (.bge 7) 3 args frame [.scalar (.i32 0), .scalar (.i32 1)] m = .ok (.next 7 [] frame m) := by
  rfl
example : step body (.bge 7) 3 args frame [.scalar (.i32 1), .scalar (.i32 0)] m = .ok (.next 4 [] frame m) := by
  rfl

example {r : Reference} (h : step body (.call 2 1) pc args frame stack m = .ok (.construct 2 args stack frame' r .word64 m')) :
    False := by
  obtain ⟨_, _, _, contradiction⟩ := step_call_action h
  cases contradiction

example {argc} (h : step body (.newVector256 2 argc) pc args frame stack m = .ok (.call 2 args stack m')) :
    False := by
  obtain ⟨_, _, _, _, _, _, contradiction⟩ := step_newVector256_action h
  cases contradiction

#print axioms step_next_target
#print axioms step_call_action
#print axioms step_newVector256_action
#print axioms step_newAggregate_action
#print axioms step_callee

end Tests.StepFlow
