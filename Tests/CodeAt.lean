import CIL.Safety.CodeAt
import CIL.Safety.SymbolicExecution

/-!
# Code placement tests

Segment theorems stated over an abstract body with `CodeAt` instead of
`body.code = leading ++ segment ++ tail`: the checked stepping tactics take the lookups that
`CodeAt.lookup` derives, placements of a larger region split into the segments a proof steps,
and a concrete body discharges the placement by `decide +kernel`.
-/

namespace Tests.CodeAt

open CIL.Safety

/-- The segment `left + right` over the first two arguments. -/
def sumSegment : List CIL.Op := [.arg 0, .arg 1, .add]

/-- Placing `sumSegment` at any `start` of a body is enough to run it: from `start` the run
    reaches `start + 3` with the sum pushed. The only facts about the body are its lookup in
    the program and the placement. -/
theorem run_sum_segment {program : CIL.Program} {method fuel start : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (placed : CodeAt body start sumSegment)
    (memory : Memory) (frame : Frame) (left right : CIL.W64) :
    run program (fuel + 3) method start [.scalar (.i64 left), .scalar (.i64 right)] frame []
        memory =
      run program fuel method (start + 3) [.scalar (.i64 left), .scalar (.i64 right)] frame
        [.scalar (.i64 (left + right))] memory := by
  -- Without the placement's lookups the abstract body cannot be stepped.
  fail_if_success cil_checked_steps [found]
  have loadLeft : body.code[start]? = some (.arg 0) := placed.lookup (index := 0) rfl
  have loadRight : body.code[start + 1]? = some (.arg 1) := placed.lookup (index := 1) rfl
  have addition : body.code[start + 2]? = some .add := placed.lookup (index := 2) rfl
  cil_checked_steps [found, loadLeft, loadRight, addition]

#print axioms run_sum_segment

/-- A placed region containing `sumSegment` runs it, through the segment theorem applied to
    the region's middle placement. -/
theorem run_sum_in_region {program : CIL.Program} {method fuel : Nat} {body : CIL.Method}
    (found : program[method]? = some body)
    (placed : CodeAt body 2 ([.nop, .nop] ++ sumSegment ++ [.ret]))
    (memory : Memory) (frame : Frame) (left right : CIL.W64) :
    run program (fuel + 3) method 4 [.scalar (.i64 left), .scalar (.i64 right)] frame []
        memory =
      run program fuel method 7 [.scalar (.i64 left), .scalar (.i64 right)] frame
        [.scalar (.i64 (left + right))] memory :=
  run_sum_segment found placed.middle memory frame left right

#print axioms run_sum_in_region

/-- A concrete body holding `sumSegment` at pc 4. -/
@[cil_code] def placedMethod : CIL.Method := {
  code := [.nop, .nop, .nop, .nop, .arg 0, .arg 1, .add, .ret]
  locals := [], returnsValue := true }

-- Placement is decided both ways on a concrete body.
example : CodeAt placedMethod 4 sumSegment := by decide +kernel
example : ¬ CodeAt placedMethod 3 sumSegment := by decide +kernel

/-- The segment theorem instantiates at a concrete program once its placement is decided. -/
theorem run_placed_method (memory : Memory) (frame : Frame) (left right : CIL.W64) :
    run [placedMethod] 5 0 4 [.scalar (.i64 left), .scalar (.i64 right)] frame [] memory =
      run [placedMethod] 2 0 7 [.scalar (.i64 left), .scalar (.i64 right)] frame
        [.scalar (.i64 (left + right))] memory :=
  run_sum_segment (fuel := 2) rfl (by decide +kernel) memory frame left right

#print axioms run_placed_method

-- The positional hypotheses an older segment theorem threads give the same placement.
example {body : CIL.Method} {tail : List CIL.Op}
    (positioned : body.code = [.nop, .nop, .nop, .nop] ++ sumSegment ++ tail) :
    CodeAt body 4 sumSegment :=
  CodeAt.of_eq_append positioned rfl

end Tests.CodeAt
