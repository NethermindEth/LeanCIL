import CIL.Safety.CodeAt
import CIL.Safety.SymbolicExecution

/-!
# Code placement tests

Segment theorems stated over an abstract body with `CodeAt` instead of
`body.code = leading ++ segment ++ tail`: the checked stepping tactics take the lookups that
`CodeAt.lookup` derives, placements of a larger region split into the segments a proof steps,
and a concrete body discharges the placement by `rfl`.
-/

namespace Tests.CodeAt

open CIL.Safety

/-- The segment `left + right` over the first two arguments. -/
def sumSegment : List CIL.Op := [.arg 0, .arg 1, .add]

-- Without a placement the abstract body's instructions are unknown, so stepping cannot start.
/-- error: cil_checked_steps took no step: the method or instruction lookup -/
#guard_msgs (substring := true) in
example {program : CIL.Program} {method fuel start : Nat} {body : CIL.Method}
    (found : program[method]? = some body) (memory : Memory) (frame : Frame)
    (left right : CIL.W64) :
    run program (fuel + 3) method start [.scalar (.i64 left), .scalar (.i64 right)] frame []
        memory =
      run program fuel method (start + 3) [.scalar (.i64 left), .scalar (.i64 right)] frame
        [.scalar (.i64 (left + right))] memory := by
  cil_checked_steps [found]

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
  cil_checked_steps [found, placed]

/-- Nested additions and a single offset fetch the same placed instruction. -/
theorem lookup_nested {body : CIL.Method} {start : Nat}
    (placed : CodeAt body start sumSegment) :
    body.code[start + 1 + 1]? = some .add ∧ body.code[start + 2]? = some .add := by
  constructor <;> cil_lookup [placed]

#print axioms lookup_nested

/-- A supplied placement expression is enough even without a local placement hypothesis. -/
theorem lookup_supplied {body : CIL.Method} {start : Nat}
    (region : CodeAt body start (sumSegment ++ [.ret])) :
    body.code[start + 2]? = some .add := by
  cil_lookup [region.append_left]

#print axioms lookup_supplied

/-- A placement cannot justify another instruction, body, or an index outside its segment. -/
theorem placement_limits {body other : CIL.Method} {start : Nat}
    (_placed : CodeAt body start sumSegment) : True := by
  fail_if_success have : body.code[start + 2]? = some .ret := by cil_lookup [_placed]
  fail_if_success have : body.code[start + 3]? = some .ret := by cil_lookup [_placed]
  fail_if_success have : other.code[start]? = some (.arg 0) := by cil_lookup [_placed]
  trivial

#print axioms placement_limits

/-- info: 'Tests.CodeAt.run_sum_segment' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run_sum_segment

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

/-- info: 'Tests.CodeAt.run_sum_in_region' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run_sum_in_region

/-- A concrete body holding `sumSegment` at pc 4. -/
def placedMethod : CIL.Method := {
  code := [.nop, .nop, .nop, .nop, .arg 0, .arg 1, .add, .ret]
  locals := [], returnsValue := true }

-- A concrete placement closes by `rfl`; a shifted one is refuted by the instruction it misplaces.
example : CodeAt placedMethod 4 sumSegment := rfl
example : ¬ CodeAt placedMethod 3 sumSegment := by
  intro placed
  cases placed.lookup 0 rfl

/-- The segment theorem instantiates at a concrete program once its placement is checked. -/
theorem run_placed_method (memory : Memory) (frame : Frame) (left right : CIL.W64) :
    run [placedMethod] 5 0 4 [.scalar (.i64 left), .scalar (.i64 right)] frame [] memory =
      run [placedMethod] 2 0 7 [.scalar (.i64 left), .scalar (.i64 right)] frame
        [.scalar (.i64 (left + right))] memory :=
  run_sum_segment (fuel := 2) (start := 4) (body := placedMethod) rfl rfl memory frame
    left right

/-- info: 'Tests.CodeAt.run_placed_method' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms run_placed_method

-- The positional hypotheses an older segment theorem threads give the same placement.
example {body : CIL.Method} {tail : List CIL.Op}
    (positioned : body.code = [.nop, .nop, .nop, .nop] ++ sumSegment ++ tail) :
    CodeAt body 4 sumSegment :=
  CodeAt.of_eq_append positioned rfl

-- Adjacent placements compose, and the parts come back out at the same positions.
example {body : CIL.Method} (first : CodeAt body 4 sumSegment) (second : CodeAt body 7 [.ret]) :
    CodeAt body 4 (sumSegment ++ [.ret]) ∧ CodeAt body 5 [.arg 1, .add, .ret] ∧
      CodeAt body 4 [.arg 0] :=
  let whole := first.append second
  ⟨whole, whole.drop 1, whole.take 1⟩

-- Dropping or taking past the end leaves the empty placement, not an out-of-range claim.
example {body : CIL.Method} (placed : CodeAt body 4 sumSegment) :
    CodeAt body 9 [] ∧ CodeAt body 4 sumSegment :=
  ⟨placed.drop 5, placed.take 5⟩

-- Within the code, a placement recovers the positional hypotheses it replaces.
example {body : CIL.Method} (placed : CodeAt body 4 sumSegment)
    (inBounds : 4 ≤ body.code.length) :
    ∃ leading tail, body.code = leading ++ sumSegment ++ tail ∧ leading.length = 4 :=
  placed.exists_eq_append inBounds

-- The bound is needed: the empty segment is placed past the end of any code.
example : CodeAt placedMethod 100 [] := CodeAt.nil
example : ¬ ∃ leading tail : List CIL.Op,
    placedMethod.code = leading ++ [] ++ tail ∧ leading.length = 100 := by
  rintro ⟨leading, tail, split, length⟩
  have total := congrArg List.length split
  simp [placedMethod] at total
  omega

-- A placement's first instruction is at its start, and the rest follows it.
example {body : CIL.Method} (placed : CodeAt body 4 sumSegment) :
    body.code[4]? = some (.arg 0) ∧ CodeAt body 5 [.arg 1, .add] :=
  CodeAt.cons_iff.mp placed

-- A nonempty placement lies within the code, so it recovers the positional form on its own.
example {body : CIL.Method} (placed : CodeAt body 4 sumSegment) :
    ∃ leading tail, body.code = leading ++ sumSegment ++ tail ∧ leading.length = 4 :=
  placed.exists_eq_append (by
    have ends := placed.end_le_length (by simp [sumSegment])
    simp only [sumSegment, List.length_cons, List.length_nil] at ends
    omega)
example : ¬ CodeAt placedMethod 6 sumSegment := fun placed =>
  absurd (placed.end_le_length (by simp [sumSegment])) (by simp [placedMethod, sumSegment])

end Tests.CodeAt
