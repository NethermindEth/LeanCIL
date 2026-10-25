import Extracted
import Examples.Support
import CIL.Safety.StepComposition
import CIL.Safety.TupleDivision

open CIL CIL.Safety
namespace ExampleProof

def inputs (lower upper divisor : W64) : List CIL.Safety.Value :=
  [.scalar (.i64 lower), .scalar (.i64 upper), .scalar (.i64 divisor)]

def frame : Frame := ⟨0, [], [], [], 0⟩

theorem run_fault {fuel pc : Nat} {op : CIL.Op} {args stack : List CIL.Safety.Value}
    {fault : ExecutionFault} (instructionFound : Extracted.method0.code[pc]? = some op)
    (failed : CIL.Safety.step Extracted.method0 op pc args frame stack Examples.empty = .error fault) :
    CIL.Safety.run Extracted.program (fuel + 1) 0 pc args frame stack Examples.empty = .error ⟨0, pc, fault⟩ := by
  simp only [CIL.Safety.run, show Extracted.program[0]? = some Extracted.method0 from rfl, instructionFound,
    failed, Except.mapError, Bind.bind, Except.bind]

theorem divRem_step (lower upper divisor : W64) :
    CIL.Safety.step Extracted.method0 (.intrinsic (.x86Base .divRem64) 3) 3 (inputs lower upper divisor) frame
      [.scalar (.i64 divisor), .scalar (.i64 upper), .scalar (.i64 lower)] Examples.empty =
      (checkedIntrinsic (.x86Base .divRem64) [.i64 lower, .i64 upper, .i64 divisor]).bind fun value => do
        return .next 4 [← checkedValue Examples.empty (.scalar value)] frame Examples.empty := rfl

/-- `DivRem(lower, upper, divisor).Quotient` is the natural quotient when it fits, and faults otherwise. -/
theorem correctness (lower upper divisor : W64) :
    (upper.toNat < divisor.toNat → ∃ quotient : W64,
      (CIL.Safety.invoke Extracted.program 8 0 (inputs lower upper divisor) Examples.empty).map Prod.snd =
        .ok [.scalar (.i64 quotient)] ∧
      quotient.toNat = (upper.toNat * 2 ^ 64 + lower.toNat) / divisor.toNat) ∧
    (divisor.toNat ≤ upper.toNat →
      CIL.Safety.invoke Extracted.program 8 0 (inputs lower upper divisor) Examples.empty =
        .error ⟨0, 3, .arithmetic (if divisor = 0 then .divideByZero else .overflow)⟩) := by
  have start : CIL.Safety.invoke Extracted.program 8 0 (inputs lower upper divisor) Examples.empty =
      CIL.Safety.run Extracted.program 5 0 3 (inputs lower upper divisor) frame
        [.scalar (.i64 divisor), .scalar (.i64 upper), .scalar (.i64 lower)] Examples.empty := rfl
  constructor
  · intro fits
    obtain ⟨quotient, remainder, evaluated, item1, -, exact, -⟩ :=
      divRem_fields (lower := lower) fits [] Examples.empty
    refine ⟨quotient, ?_, exact⟩
    have field : CIL.Safety.step Extracted.method0 (.fieldAt 0 8) 4 (inputs lower upper divisor) frame
        [.scalar (.aggregate (X86.wordBytes quotient ++ X86.wordBytes remainder))] Examples.empty =
        .ok (.next 5 [.scalar (.i64 quotient)] frame Examples.empty) := by
      change ((do
        let (memory, values) ← instruction (.fieldAt 0 8)
          [.scalar (.aggregate (X86.wordBytes quotient ++ X86.wordBytes remainder))] Examples.empty
        return FrameAction.next 5 values frame memory) : ExecutionResult FrameAction) = _
      rw [item1]
      rfl
    rw [start, run_next (by rfl) (by rfl) (by rw [divRem_step, evaluated]; rfl),
      run_next (by rfl) (by rfl) field]
    rfl
  · intro overflows
    rw [start]
    apply run_fault (by rfl)
    rw [divRem_step, divRem_fault overflows]
    rfl

#print axioms correctness
end ExampleProof
