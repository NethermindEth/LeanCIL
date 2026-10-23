import Extracted
import Examples.Support
import CIL.Safety.StepComposition

open CIL CIL.Safety
namespace ExampleProof

/-- Reading the nested value copies exactly its bytes, including padding. -/
theorem correctness (bytes : List (BitVec 8)) (size : bytes.length = 32) :
    (invoke Extracted.program 3 0 [.scalar (.aggregate bytes)] Examples.empty).map Prod.snd =
      .ok [.scalar (.aggregate ((bytes.drop 8).take 16))] := by
  let args : List CIL.Safety.Value := [.scalar (.aggregate bytes)]
  let frame : Frame := ⟨0, [], [], []⟩
  have first : step Extracted.method0 (.arg 0) 0 args frame [] Examples.empty =
      .ok (.next 1 args frame Examples.empty) := rfl
  have second : step Extracted.method0 (.aggregateFieldAt 8 16) 1 args frame args Examples.empty =
      .ok (.next 2 [.scalar (.aggregate ((bytes.drop 8).take 16))] frame Examples.empty) := by
    simp [CIL.Safety.step, pureArity, instruction, observerCount, unspecifiedOperands,
      CIL.Safety.Value.hasUnspecified, CIL.Value.hasUnspecified,
      args, size, Pure.pure, Except.pure, Bind.bind, Except.bind]
  have ran : run Extracted.program 3 0 0 args frame [] Examples.empty =
      .ok (Examples.empty, [.scalar (.aggregate ((bytes.drop 8).take 16))]) := by
    rw [run_next Extracted.lookup0 Extracted.method0_instruction0 first]
    rw [run_next Extracted.lookup0 Extracted.method0_instruction1 second]
    rfl
  have invoked := invoke_of_run (memory := Examples.empty) Extracted.lookup0 (by rfl) (by rfl) ran
  rw [invoked]
  rfl

#print axioms correctness
end ExampleProof
