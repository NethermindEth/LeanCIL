import Extracted
import Examples.Support
import CIL.Safety.StepComposition
import CIL.Safety.TupleDivision

/-!
# Math.DivRem quotient contract

`Math.DivRem(left, right).Quotient` on `int` is the truncated quotient, and the call raises
exactly the faults of CIL `div`: `DivideByZeroException` for a zero divisor and
`OverflowException` for `int.MinValue / -1`.
-/

open CIL CIL.Safety
namespace ExampleProof

/-- The two `int` arguments as stack values. -/
def inputs (left right : W32) : List CIL.Safety.Value := [.scalar (.i32 left), .scalar (.i32 right)]

/-- The activation after both arguments are loaded. -/
def frame : Frame := ⟨0, [], [], [], 0⟩

/-- A failing step at `pc` is the located fault of the whole run. -/
theorem run_fault {fuel pc : Nat} {op : CIL.Op} {args stack : List CIL.Safety.Value}
    {fault : ExecutionFault} (instructionFound : Extracted.method0.code[pc]? = some op)
    (failed :
      CIL.Safety.step Extracted.method0 op pc args frame stack Examples.empty = .error fault) :
    CIL.Safety.run Extracted.program (fuel + 1) 0 pc args frame stack Examples.empty =
      .error ⟨0, pc, fault⟩ := by
  simp only [CIL.Safety.run, show Extracted.program[0]? = some Extracted.method0 from rfl,
    instructionFound, failed, Except.mapError, Bind.bind, Except.bind]

/-- The runtime call is the checked `divRem 32 true` intrinsic at pc 2. -/
theorem divRem_step (left right : W32) :
    CIL.Safety.step Extracted.method0 (.intrinsic (.scalar (.divRem 32 true)) 2) 2
      (inputs left right) frame [.scalar (.i32 right), .scalar (.i32 left)] Examples.empty =
      (checkedIntrinsic (.scalar (.divRem 32 true)) [.i32 left, .i32 right]).bind fun value => do
        return .next 3 [← checkedValue Examples.empty (.scalar value)] frame Examples.empty := rfl

/-- The invocation reaches the runtime call with both arguments on the stack. -/
theorem start (left right : W32) :
    CIL.Safety.invoke Extracted.program 8 0 (inputs left right) Examples.empty =
      CIL.Safety.run Extracted.program 6 0 2 (inputs left right) frame
        [.scalar (.i32 right), .scalar (.i32 left)] Examples.empty := rfl

/-- A zero divisor or `MinValue / -1` is the located `div` fault, never a tuple. -/
theorem fault_of_divRem {left right : W32} {fault : ArithmeticFault}
    (failed : divRemBits true left right = .error fault) :
    CIL.Safety.invoke Extracted.program 8 0 (inputs left right) Examples.empty =
      .error ⟨0, 2, .arithmetic fault⟩ := by
  rw [start]
  apply run_fault (by rfl)
  rw [divRem_step, mathDivRem32_eq, failed]
  rfl

/-- `Math.DivRem(left, right).Quotient` returns the exact truncated quotient whenever `div`
    succeeds, and otherwise raises its divide-by-zero or overflow fault. -/
theorem correctness (left right : W32) :
    (right ≠ 0 → (left ≠ BitVec.intMin 32 ∨ right ≠ -1) → ∃ quotient : W32,
      (CIL.Safety.invoke Extracted.program 8 0 (inputs left right) Examples.empty).map Prod.snd =
        .ok [.scalar (.i32 quotient)] ∧
      quotient.toInt = left.toInt.tdiv right.toInt) ∧
    CIL.Safety.invoke Extracted.program 8 0 (inputs left 0) Examples.empty =
      .error ⟨0, 2, .arithmetic .divideByZero⟩ ∧
    CIL.Safety.invoke Extracted.program 8 0 (inputs (BitVec.intMin 32) (-1)) Examples.empty =
      .error ⟨0, 2, .arithmetic .overflow⟩ := by
  refine ⟨fun nonzero representable => ?_, fault_of_divRem (divRemBits_zero true left),
    fault_of_divRem (divRemBits_overflow (by decide))⟩
  obtain ⟨evaluated, exact, -⟩ := divRemBits_signed (by decide) nonzero representable
  refine ⟨left.sdiv right, ?_, exact⟩
  have call : CIL.Safety.step Extracted.method0 (.intrinsic (.scalar (.divRem 32 true)) 2) 2
      (inputs left right) frame [.scalar (.i32 right), .scalar (.i32 left)] Examples.empty =
      .ok (.next 3 [.scalar (.aggregate (numberBytes (left.sdiv right).toNat 4 ++
        numberBytes (left.srem right).toNat 4))] frame Examples.empty) := by
    rw [divRem_step, mathDivRem32_eq, evaluated]
    rfl
  have field : CIL.Safety.step Extracted.method0 (.fieldAt 0 4) 3 (inputs left right) frame
      [.scalar (.aggregate (numberBytes (left.sdiv right).toNat 4 ++
        numberBytes (left.srem right).toNat 4))] Examples.empty =
      .ok (.next 4 [.scalar (.i32 (left.sdiv right))] frame Examples.empty) := by
    change ((do
      let (memory, values) ← instruction (.fieldAt 0 4)
        [.scalar (.aggregate (numberBytes (left.sdiv right).toNat 4 ++
          numberBytes (left.srem right).toNat 4))] Examples.empty
      return FrameAction.next 4 values frame memory) : ExecutionResult FrameAction) = _
    rw [item1_of_int_tuple]
    rfl
  rw [start, run_next (by rfl) (by rfl) call, run_next (by rfl) (by rfl) field]
  rfl

#print axioms correctness
end ExampleProof
