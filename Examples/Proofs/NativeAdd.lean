import Extracted
import Examples.Support
import CIL.Safety.StepComposition

open CIL CIL.Safety
namespace ExampleProof

/-- Native addition on the admitted 64-bit target is modular word addition. -/
theorem correctness (x y : W64) :
    (CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i64 x), .scalar (.i64 y)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i64 (x + y))] := by
  let args : List CIL.Safety.Value := [.scalar (.i64 x), .scalar (.i64 y)]
  let frame : Frame := ⟨0, [], [], [], 0⟩
  have first : CIL.Safety.step Extracted.method0 (.arg 0) 0 args frame [] Examples.empty =
      .ok (.next 1 [.scalar (.i64 x)] frame Examples.empty) := rfl
  have second : CIL.Safety.step Extracted.method0 (.arg 1) 1 args frame [.scalar (.i64 x)] Examples.empty =
      .ok (.next 2 [.scalar (.i64 y), .scalar (.i64 x)] frame Examples.empty) := rfl
  have added : CIL.Safety.step Extracted.method0 .add 2 args frame
      [.scalar (.i64 y), .scalar (.i64 x)] Examples.empty =
      .ok (.next 3 [.scalar (.i64 (x + y))] frame Examples.empty) := rfl
  have ran : CIL.Safety.run Extracted.program 4 0 0 args frame [] Examples.empty =
      .ok (Examples.empty, [.scalar (.i64 (x + y))]) := by
    rw [run_next Extracted.lookup0 Extracted.method0_instruction0 first]
    rw [run_next Extracted.lookup0 Extracted.method0_instruction1 second]
    rw [run_next Extracted.lookup0 Extracted.method0_instruction2 added]
    rfl
  have invoked := invoke_of_run (memory := Examples.empty) Extracted.lookup0 (by rfl) (by rfl) ran
  rw [invoked]
  rfl

#print axioms correctness
end ExampleProof
