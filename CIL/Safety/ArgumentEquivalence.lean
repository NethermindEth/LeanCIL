import CIL.Safety.Execution

/-!
# Unobserved arguments

After frame setup, the checked interpreter reads the argument list only through `ldarg`.
Two argument lists that agree on every index the body loads therefore give the same
`step`, `run` and `invoke` results, so a proof may replace arguments the method never reads.
-/

namespace CIL.Safety

/-- Only argument loads observe the argument list after frame setup. -/
theorem step_arguments_eq (body : CIL.Method) (op : CIL.Instruction) (pc : Nat)
    (args other : List Value) (frame : Frame) (stack : List Value) (memory : Memory)
    (agreement : ∀ index, op = .ldarg index → args[index]? = other[index]?) :
    step body op pc args frame stack memory = step body op pc other frame stack memory := by
  cases op <;> try rfl
  case ldarg index =>
    have same : loadArgument body index args frame memory =
        loadArgument body index other frame memory := by
      simp only [loadArgument, agreement index rfl]
    exact congrArg (fun (loaded : ExecutionResult Value) =>
      show ExecutionResult FrameAction from do
        return FrameAction.next (pc + 1) ((← loaded) :: stack) frame memory) same
  all_goals
    cases stack with
    | nil => rfl
    | cons value rest =>
      first
      | rfl
      | cases rest with
        | nil =>
          first | rfl | (cases value <;> first | rfl |
            (rename_i reference; cases reference <;> rfl))
        | cons next rest =>
          first | rfl | (cases value <;> first | rfl | (cases next <;> rfl) |
            (rename_i reference; cases reference <;> first | rfl | (cases next <;> rfl)))

/-- Changing unobserved arguments preserves every checked execution step.
    Child calls receive the same evaluated stack arguments on both sides. -/
theorem run_arguments_eq (program : CIL.Program) (method : Nat) (body : CIL.Method)
    (lookup : program[method]? = some body) (args other : List Value)
    (agreement : ∀ index, CIL.Instruction.ldarg index ∈ body.code → args[index]? = other[index]?)
    (fuel pc : Nat) (frame : Frame) (stack : List Value) (memory : Memory) :
    run program fuel method pc args frame stack memory =
      run program fuel method pc other frame stack memory := by
  induction fuel generalizing pc frame stack memory with
  | zero => rfl
  | succ fuel ih =>
    cases fetched : body.code[pc]? with
    | none => simp [run, lookup, fetched]
    | some op =>
      have same := step_arguments_eq body op pc args other frame stack memory (by
        intro index equal
        subst op
        exact agreement index (List.mem_of_getElem? fetched))
      simp only [run, lookup, fetched]
      rw [same]
      cases haction : step body op pc other frame stack memory with
      | error fault => rfl
      | ok action =>
        cases action with
        | next target values frame memory =>
          simpa only [Except.mapError, Bind.bind, Except.bind] using ih target frame values memory
        | returned values memory => rfl
        | tailCall callee arguments memory => rfl
        | call callee arguments rest memory =>
          simp only [Except.mapError, Bind.bind, Except.bind, ih]
        | construct callee arguments rest frame temporary kind memory =>
          simp only [Except.mapError, Bind.bind, Except.bind, ih]

/-- `invoke` agrees on two argument lists that are both checked, agree where the body loads
    them, and set up the same frame. -/
theorem invoke_arguments_eq (program : CIL.Program) (method : Nat) (body : CIL.Method)
    (lookup : program[method]? = some body) (args other : List Value)
    (agreement : ∀ index, CIL.Instruction.ldarg index ∈ body.code → args[index]? = other[index]?)
    (fuel : Nat) (memory : Memory)
    (checkedArgs : args.mapM (checkedValue memory) = .ok args)
    (checkedOther : other.mapM (checkedValue memory) = .ok other)
    (setup : enterFrame body args memory = enterFrame body other memory) :
    invoke program fuel method args memory = invoke program fuel method other memory := by
  simp only [invoke, lookup, checkedArgs, checkedOther, Except.mapError, Bind.bind, Except.bind]
  rw [setup]
  cases setupResult : enterFrame body other memory with
  | error fault => rfl
  | ok pair =>
    rcases pair with ⟨frame, entered⟩
    exact run_arguments_eq program method body lookup args other agreement fuel 0 frame [] entered

#print axioms step_arguments_eq
#print axioms run_arguments_eq
#print axioms invoke_arguments_eq
end CIL.Safety
