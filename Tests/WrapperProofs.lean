import CIL.Safety.StepComposition

namespace Tests.WrapperProofs

/-- An instruction fault terminates the checked execution at its actual site. -/
theorem run_fault {program : CIL.Program} {fuel method pc : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack : List CIL.Safety.Value}
    {frame : CIL.Safety.Frame} {memory : CIL.Safety.Memory}
    {fault : CIL.Safety.ExecutionFault}
    (found : program[method]? = some body) (instruction : body.code[pc]? = some op)
    (failed : CIL.Safety.step body op pc args frame stack memory = .error fault) :
    CIL.Safety.run program (fuel + 1) method pc args frame stack memory =
      .error ⟨method, pc, fault⟩ := by
  simp only [CIL.Safety.run, found, instruction, failed, Except.mapError,
    Bind.bind, Except.bind]

/-- Simplify one known intrinsic step, without unfolding the recursive interpreter. -/
macro "math_wrapper_step " evaluated:term : tactic => `(tactic|
  (simp only [CIL.Safety.step, CIL.Intrinsic.available, Bool.not_true, Bool.false_eq_true,
    List.length_cons, List.length_nil, Nat.reduceAdd, ite_false,
    List.take, List.reverse, List.reverseAux, CIL.Safety.scalars, CIL.Safety.numericValue,
    ite_true, Bind.bind, Except.bind, Pure.pure, Except.pure,
    CIL.Safety.checkedIntrinsic, $evaluated:term, Except.mapError,
    CIL.Safety.checkedValue, List.drop] <;> rfl))

end Tests.WrapperProofs
