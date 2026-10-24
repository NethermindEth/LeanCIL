import CIL.Safety.OutcomeContract

/-!
# Runtime exceptions

`Raises` covers only explicit `throw`s. `RaisesCLR` also counts faults the CLR turns into
exceptions: checked overflow (`System.OverflowException`) and division by zero
(`System.DivideByZeroException`). `OutcomeContract.HoldsCLR` is `Holds` read through this
mapping, and the lemmas mirror the call-composition lemmas of `CIL.Safety.OutcomeContract`.
-/

namespace CIL.Safety

/-- The CLR exception a fault surfaces as, if any; other faults are not exceptions. -/
def ExecutionFault.clrException : ExecutionFault → Option String
  | .thrown exception => some exception
  | .arithmetic .overflow => some "System.OverflowException"
  | .arithmetic .divideByZero => some "System.DivideByZeroException"
  | _ => none

/-- Some invocation fails with a fault that surfaces as exactly `exception`. -/
def RaisesCLR (program : CIL.Program) (method : Nat) (args : List Value)
    (memory : Memory) (exception : String) : Prop :=
  ∃ fuel fault, invoke program fuel method args memory = .error fault ∧
    fault.fault.clrException = some exception

/-- `RaisesCLR` for a run already in progress at `pc`. -/
def RunRaisesCLR (program : CIL.Program) (method pc : Nat) (args : List Value)
    (frame : Frame) (stack : List Value) (memory : Memory) (exception : String) : Prop :=
  ∃ fuel fault, run program fuel method pc args frame stack memory = .error fault ∧
    fault.fault.clrException = some exception

/-- A fault that names a CLR exception is not fuel exhaustion, so more fuel cannot change it. -/
theorem settled_of_clrException {fault : LocatedFault} {exception : String}
    (named : fault.fault.clrException = some exception) :
    Settled (.error fault : Except LocatedFault α) := by
  cases fault with
  | mk method pc fault =>
    cases fault <;> simp_all [ExecutionFault.clrException, Settled]

theorem RaisesCLR.of_raises {program : CIL.Program} {method : Nat} {args : List Value}
    {memory : Memory} {exception : String}
    (raised : Raises program method args memory exception) :
    RaisesCLR program method args memory exception := by
  obtain ⟨fuel, fault, invoked, thrown⟩ := raised
  exact ⟨fuel, fault, invoked, by simp [thrown, ExecutionFault.clrException]⟩

theorem RaisesCLR.of_invoke {program : CIL.Program} {fuel method : Nat} {args : List Value}
    {memory : Memory} {fault : LocatedFault} {exception : String}
    (invoked : invoke program fuel method args memory = .error fault)
    (named : fault.fault.clrException = some exception) :
    RaisesCLR program method args memory exception :=
  ⟨fuel, fault, invoked, named⟩

/-- A settled invocation result that names a different exception, or none, refutes
    `RaisesCLR`. -/
theorem RaisesCLR.not_of_invoke {program : CIL.Program} {fuel method : Nat} {args : List Value}
    {memory : Memory} {fault : LocatedFault} {exception : String}
    (settled : Settled (.error fault : Except LocatedFault (Memory × List Value)))
    (invoked : invoke program fuel method args memory = .error fault)
    (different : fault.fault.clrException ≠ some exception) :
    ¬ RaisesCLR program method args memory exception := by
  rintro ⟨otherFuel, otherFault, otherInvoked, named⟩
  have same : fault = otherFault := Except.error.inj
    (invoke_unique settled (settled_of_clrException named) invoked otherInvoked)
  subst otherFault
  exact different named

/-- `OutcomeContract.Holds` with named exceptions read as `RaisesCLR`, so a contract may name
    the exception a checked overflow or a division by zero raises. -/
def OutcomeContract.HoldsCLR {Input Output : Type} (c : OutcomeContract Input Output)
    (program : CIL.Program) (method : Nat) : Prop :=
  ∀ input initial, c.pre input initial →
    match c.raises input initial with
    | some exception => RaisesCLR program method (c.args input) initial exception
    | none =>
      ∃ fuel final values,
        invoke program fuel method (c.args input) initial = .ok (final, values) ∧
        Confined (c.footprint input) initial final ∧ c.Returns input initial final values

theorem OutcomeContract.HoldsCLR.raising {Input Output : Type} {c : OutcomeContract Input Output}
    {program : CIL.Program} {method : Nat} {input : Input} {initial : Memory} {exception : String}
    (holds : c.HoldsCLR program method) (permitted : c.pre input initial)
    (raised : c.raises input initial = some exception) :
    RaisesCLR program method (c.args input) initial exception := by
  have outcome := holds input initial permitted
  rw [raised] at outcome
  exact outcome

theorem OutcomeContract.HoldsCLR.returning {Input Output : Type} {c : OutcomeContract Input Output}
    {program : CIL.Program} {method : Nat} {input : Input} {initial : Memory}
    (holds : c.HoldsCLR program method) (permitted : c.pre input initial)
    (normal : c.raises input initial = none) :
    ∃ fuel final values,
      invoke program fuel method (c.args input) initial = .ok (final, values) ∧
      Confined (c.footprint input) initial final ∧ c.Returns input initial final values := by
  have outcome := holds input initial permitted
  rw [normal] at outcome
  exact outcome

/-- Every proved `OutcomeContract.Holds` also holds in the CLR reading. -/
theorem OutcomeContract.Holds.clr {Input Output : Type} {c : OutcomeContract Input Output}
    {program : CIL.Program} {method : Nat} (holds : c.Holds program method) :
    c.HoldsCLR program method := by
  intro input initial permitted
  cases named : c.raises input initial with
  | none => exact holds.returning permitted named
  | some exception => exact RaisesCLR.of_raises (holds.raising permitted named)

theorem raisesCLR_of_run {program : CIL.Program} {method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered : Memory} {exception : String}
    (found : program[method]? = some body)
    (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (raised : RunRaisesCLR program method 0 args frame [] entered exception) :
    RaisesCLR program method args memory exception := by
  obtain ⟨fuel, fault, ran, named⟩ := raised
  refine ⟨fuel, fault, ?_, named⟩
  simp only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind]
  exact ran

theorem run_next_raisesCLR {program : CIL.Program} {method pc target : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {exception : String}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory =
      .ok (.next target values nextFrame updated))
    (continuation : RunRaisesCLR program method target args nextFrame values updated exception) :
    RunRaisesCLR program method pc args frame stack memory exception := by
  obtain ⟨fuel, fault, ran, named⟩ := continuation
  exact ⟨fuel + 1, fault, (run_next methodFound instructionFound stepped).trans ran, named⟩

/-- A run raises at a step whose fault surfaces as a CLR exception. -/
theorem run_fault_raisesCLR {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack : List Value} {frame : Frame} {memory : Memory}
    {fault : ExecutionFault} {exception : String}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .error fault)
    (named : fault.clrException = some exception) :
    RunRaisesCLR program method pc args frame stack memory exception :=
  ⟨1, ⟨method, pc, fault⟩, by
    simp only [run, methodFound, instructionFound, stepped, Except.mapError, Bind.bind,
      Except.bind], named⟩

/-- Propagate the CLR exception a callee's contract names for this input. -/
theorem run_call_raisesCLR_of_contract {Input Output : Type} {c : OutcomeContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value} {frame : Frame} {memory updated : Memory}
    {exception : String}
    (holds : c.HoldsCLR program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory =
      .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input)
    (checked : arguments.mapM (checkedValue updated) = .ok arguments)
    (permitted : c.pre input updated) (raised : c.raises input updated = some exception) :
    RunRaisesCLR program method pc args frame stack memory exception := by
  subst encoded
  obtain ⟨fuel, fault, invoked, named⟩ := holds.raising permitted raised
  obtain ⟨located, ran, same⟩ :=
    run_call_error methodFound instructionFound stepped checked invoked
  exact ⟨fuel + 1, located, ran, by rw [same]; exact named⟩

#print axioms RaisesCLR.not_of_invoke
#print axioms OutcomeContract.Holds.clr
#print axioms run_call_raisesCLR_of_contract

end CIL.Safety
