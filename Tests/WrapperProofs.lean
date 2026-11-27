import CIL.Safety.StepComposition
import CIL.Safety.HandlerSteps

/-! Arithmetic wrapper fixtures use the resolved call's model to check its result or fault. -/

namespace Tests.WrapperProofs

/-- Select the checked call model and simplify its arithmetic result. -/
macro "math_wrapper_step " model:term:max evaluated:term : tactic => `(tactic|
  (rw [CIL.Safety.step_call_intrinsic _ _ _ _ _ rfl $model rfl]
   simp only [CIL.Safety.intrinsicCall, CIL.Intrinsic.available, Bool.not_true,
    Bool.false_eq_true, List.length_cons, List.length_nil, Nat.reduceAdd, ite_false,
    List.take, List.reverse, List.reverseAux, CIL.Safety.scalars, CIL.Safety.numericValue,
    ite_true, Bind.bind, Except.bind, Pure.pure, Except.pure,
    CIL.Safety.checkedIntrinsic, $evaluated:term, Except.mapError,
    CIL.Safety.checkedValue, List.drop] <;> rfl))

private def minimumRef : CIL.Extraction.MethodRef :=
  let int := CIL.Extraction.TypeExpr.primitive .int32
  { owner := .atom CIL.Extraction.runtimeScope "System.Math" .classType, name := name!"Min",
    hasThis := false, genericArity := 0, returnType := int, parameters := [int, int] }

/-- Returns the signed minimum of its two int arguments through the scalar math intrinsic. -/
def minimumMethod : CIL.Method := {
  code := [.ldarg 0, .ldarg 1, .call minimumRef, .ret]
  locals := [], returnsValue := true }

private theorem minimumModel :
    CIL.Extraction.runtimeModel minimumMethod.environment .call minimumRef =
      some (.intrinsic (.scalar (.math .min 32 true)) 2) := rfl

/-- The minimum intrinsic pushes the evaluator's result, stated as a generated wrapper does. -/
theorem minimum_step (left right result : CIL.W32)
    (evaluated : CIL.evalIntegerMath .min 32 true [.i32 left, .i32 right] = .ok (.i32 result)) :
    CIL.Safety.step minimumMethod (.call minimumRef) 2 []
        ⟨0, [], [], 0, []⟩ [.scalar (.i32 right), .scalar (.i32 left)] CIL.Safety.Memory.empty =
      .ok (.next 3 [.scalar (.i32 result)] ⟨0, [], [], 0, []⟩ CIL.Safety.Memory.empty) := by
  math_wrapper_step minimumModel evaluated
#print axioms minimum_step

/-- A faulting evaluation faults the minimum intrinsic with the same arithmetic fault. -/
theorem minimum_fault (left right : CIL.W32) (fault : CIL.ArithmeticFault)
    (evaluated : CIL.evalIntegerMath .min 32 true [.i32 left, .i32 right] = .error fault) :
    CIL.Safety.step minimumMethod (.call minimumRef) 2 []
        ⟨0, [], [], 0, []⟩ [.scalar (.i32 right), .scalar (.i32 left)] CIL.Safety.Memory.empty =
      .error (.arithmetic fault) := by
  math_wrapper_step minimumModel evaluated
#print axioms minimum_fault

end Tests.WrapperProofs
