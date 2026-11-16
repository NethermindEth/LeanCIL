import CIL.Safety.StepComposition

namespace Tests.WrapperProofs

/-- An instruction fault terminates the checked execution at its actual site. -/
theorem run_fault {program : CIL.Program} {fuel method pc : Nat}
    {body : CIL.Method} {op : CIL.Instruction} {args stack : List CIL.Safety.Value}
    {frame : CIL.Safety.Frame} {memory : CIL.Safety.Memory}
    {fault : CIL.Safety.ExecutionFault}
    (found : program[method]? = some body) (instruction : body.code[pc]? = some op)
    (failed : CIL.Safety.step body op pc args frame stack memory = .error fault) :
    CIL.Safety.run program (fuel + 1) method pc args frame stack memory =
      .error ⟨method, pc, fault⟩ := by
  simp only [CIL.Safety.run, found, instruction, failed, Except.mapError,
    Bind.bind, Except.bind]

/-- Simplify one known intrinsic step through its step equation, without unfolding the
    interpreter: `step` reaches an intrinsic only through `intrinsicCall`. -/
macro "math_wrapper_step " evaluated:term : tactic => `(tactic|
  (simp only [CIL.Safety.step_intrinsic_eq, CIL.Intrinsic.available, Bool.not_true,
    Bool.false_eq_true, List.length_cons, List.length_nil, Nat.reduceAdd, ite_false,
    List.take, List.reverse, List.reverseAux, CIL.Safety.scalars, CIL.Safety.numericValue,
    ite_true, Bind.bind, Except.bind, Pure.pure, Except.pure,
    CIL.Safety.checkedIntrinsic, $evaluated:term, Except.mapError,
    CIL.Safety.checkedValue, List.drop] <;> rfl))

/-- Returns the signed minimum of its two int arguments through the scalar math intrinsic. -/
def minimumMethod : CIL.Method := {
  code := [.ldarg 0, .ldarg 1, .intrinsic (.scalar (.math .min 32 true)) 2, .ret]
  locals := [], returnsValue := true }

/-- The minimum intrinsic pushes the evaluator's result, stated as a generated wrapper does. -/
theorem minimum_step (left right result : CIL.W32)
    (evaluated : CIL.evalIntegerMath .min 32 true [.i32 left, .i32 right] = .ok (.i32 result)) :
    CIL.Safety.step minimumMethod (.intrinsic (.scalar (.math .min 32 true)) 2) 2 []
        ⟨0, [], [], 0⟩ [.scalar (.i32 right), .scalar (.i32 left)] CIL.Safety.Memory.empty =
      .ok (.next 3 [.scalar (.i32 result)] ⟨0, [], [], 0⟩ CIL.Safety.Memory.empty) := by
  math_wrapper_step evaluated
#print axioms minimum_step

/-- A faulting evaluation faults the minimum intrinsic with the same arithmetic fault. -/
theorem minimum_fault (left right : CIL.W32) (fault : CIL.ArithmeticFault)
    (evaluated : CIL.evalIntegerMath .min 32 true [.i32 left, .i32 right] = .error fault) :
    CIL.Safety.step minimumMethod (.intrinsic (.scalar (.math .min 32 true)) 2) 2 []
        ⟨0, [], [], 0⟩ [.scalar (.i32 right), .scalar (.i32 left)] CIL.Safety.Memory.empty =
      .error (.arithmetic fault) := by
  math_wrapper_step evaluated
#print axioms minimum_fault

end Tests.WrapperProofs
