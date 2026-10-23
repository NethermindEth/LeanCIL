import CIL.Safety.MethodContract

namespace CIL.Safety

/-- Exactly a thrown `exception`: fuel exhaustion, unsupported instructions and other
    faults never satisfy it. With no handlers, memory after a throw is unobservable. -/
def Raises (program : CIL.Program) (method : Nat) (args : List Value) (memory : Memory) (exception : String) : Prop :=
  ∃ fuel fault, invoke program fuel method args memory = .error fault ∧ fault.fault = .thrown exception

def RunRaises (program : CIL.Program) (method pc : Nat) (args : List Value) (frame : Frame)
    (stack : List Value) (memory : Memory) (exception : String) : Prop :=
  ∃ fuel fault, run program fuel method pc args frame stack memory = .error fault ∧ fault.fault = .thrown exception

/-- A method contract that also names the exception each input raises; `none` is normal return. -/
structure OutcomeContract (Input : Type) (Output : Type := List Value) extends MethodContract Input Output where
  raises : Input → Memory → Option String

def OutcomeContract.Holds {Input Output : Type} (c : OutcomeContract Input Output) (program : CIL.Program) (method : Nat) : Prop :=
  ∀ input initial, c.pre input initial →
    match c.raises input initial with
    | some exception => Raises program method (c.args input) initial exception
    | none => ∃ fuel final values, invoke program fuel method (c.args input) initial = .ok (final, values) ∧
        Confined (c.footprint input) initial final ∧ c.Returns input initial final values

theorem OutcomeContract.Holds.raising {Input Output : Type} {c : OutcomeContract Input Output} {program : CIL.Program}
    {method : Nat} {input : Input} {initial : Memory} {exception : String}
    (holds : c.Holds program method) (permitted : c.pre input initial) (raised : c.raises input initial = some exception) :
    Raises program method (c.args input) initial exception := by
  have outcome := holds input initial permitted
  rw [raised] at outcome
  exact outcome

theorem OutcomeContract.Holds.returning {Input Output : Type} {c : OutcomeContract Input Output} {program : CIL.Program}
    {method : Nat} {input : Input} {initial : Memory}
    (holds : c.Holds program method) (permitted : c.pre input initial) (normal : c.raises input initial = none) :
    ∃ fuel final values, invoke program fuel method (c.args input) initial = .ok (final, values) ∧
      Confined (c.footprint input) initial final ∧ c.Returns input initial final values := by
  have outcome := holds input initial permitted
  rw [normal] at outcome
  exact outcome

/-- A normal-return contract is the outcome contract that never raises. -/
theorem MethodContract.Holds.outcomes {Input Output : Type} {c : MethodContract Input Output} {program : CIL.Program}
    {method : Nat} (holds : c.Holds program method) :
    ({ c with raises := fun _ _ => none } : OutcomeContract Input Output).Holds program method :=
  holds

theorem OutcomeContract.Holds.normal {Input Output : Type} {c : OutcomeContract Input Output} {program : CIL.Program}
    {method : Nat} (holds : c.Holds program method) (never : ∀ input initial, c.pre input initial → c.raises input initial = none) :
    c.toMethodContract.Holds program method :=
  fun input initial permitted => holds.returning permitted (never input initial permitted)

/-- Successful or raised invocations agree at every fuel, so a computed run refutes a contract. -/
theorem invoke_unique {program : CIL.Program} {method left right : Nat} {args : List Value} {memory : Memory}
    {first second : Except LocatedFault (Memory × List Value)} (firstSettled : Settled first) (secondSettled : Settled second)
    (one : invoke program left method args memory = first) (other : invoke program right method args memory = second) :
    first = second := by
  have up := invoke_mono program left right method args memory first firstSettled one
  have down := invoke_mono program right left method args memory second secondSettled other
  rw [Nat.add_comm] at down
  exact up.symm.trans down

/-- A callee fault reaches the caller unchanged; only frame-entry faults are relocated to the call. -/
theorem run_call_error {program : CIL.Program} {fuel method pc callee : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {fault : LocatedFault}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (checked : arguments.mapM (checkedValue updated) = .ok arguments)
    (child : invoke program fuel callee arguments updated = .error fault) :
    ∃ located, run program (fuel + 1) method pc args frame stack memory = .error located ∧
      located.fault = fault.fault := by
  cases hb : program[callee]? with
  | none =>
    simp only [invoke, hb] at child
    cases child
    exact ⟨⟨method, pc, .invalidState⟩, by
      simp only [run, methodFound, instructionFound, stepped, hb, Except.mapError, Bind.bind, Except.bind], rfl⟩
  | some childBody =>
    cases he : enterFrame childBody arguments updated with
    | error entry =>
      simp only [invoke, hb, checked, he, Except.mapError, Bind.bind, Except.bind] at child
      cases child
      exact ⟨⟨method, pc, entry⟩, by simp only [run, methodFound, instructionFound, stepped, hb, he, Except.mapError,
        Bind.bind, Except.bind], rfl⟩
    | ok entered =>
      obtain ⟨childFrame, childMemory⟩ := entered
      simp only [invoke, hb, checked, he, Except.mapError, Bind.bind, Except.bind] at child
      exact ⟨fault, by simp only [run, methodFound, instructionFound, stepped, hb, he, child,
        Except.mapError, Bind.bind, Except.bind], rfl⟩

theorem raises_of_run {program : CIL.Program} {method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered : Memory} {exception : String}
    (found : program[method]? = some body)
    (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (raised : RunRaises program method 0 args frame [] entered exception) :
    Raises program method args memory exception := by
  obtain ⟨fuel, fault, ran, thrown⟩ := raised
  refine ⟨fuel, fault, ?_, thrown⟩
  simp only [invoke, found, checked, setup, Except.mapError, Bind.bind, Except.bind]
  exact ran

theorem run_next_raises {program : CIL.Program} {method pc target : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {exception : String}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.next target values nextFrame updated))
    (continuation : RunRaises program method target args nextFrame values updated exception) :
    RunRaises program method pc args frame stack memory exception := by
  obtain ⟨fuel, fault, ran, thrown⟩ := continuation
  exact ⟨fuel + 1, fault, (run_next methodFound instructionFound stepped).trans ran, thrown⟩

theorem run_throw_raises {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {op : CIL.Op} {args stack : List Value} {frame : Frame} {memory : Memory} {exception : String}
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .error (.thrown exception)) :
    RunRaises program method pc args frame stack memory exception :=
  ⟨1, ⟨method, pc, .thrown exception⟩, by
    simp only [run, methodFound, instructionFound, stepped, Except.mapError, Bind.bind, Except.bind], rfl⟩

/-- Propagate the exception a callee's contract names for this input. -/
theorem run_call_raises_of_contract {Input Output : Type} {c : OutcomeContract Input Output} {program : CIL.Program}
    {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {exception : String}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input)
    (checked : arguments.mapM (checkedValue updated) = .ok arguments)
    (permitted : c.pre input updated) (raised : c.raises input updated = some exception) :
    RunRaises program method pc args frame stack memory exception := by
  subst encoded
  obtain ⟨fuel, fault, invoked, thrown⟩ := holds.raising permitted raised
  obtain ⟨located, ran, same⟩ := run_call_error methodFound instructionFound stepped checked invoked
  exact ⟨fuel + 1, located, ran, same.trans thrown⟩

/-- Continue after a callee whose contract names no exception for this input. -/
theorem run_call_of_outcome {Input Output : Type} {c : OutcomeContract Input Output} {program : CIL.Program}
    {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated) (normal : c.raises input updated = none)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame (values ++ rest) final = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧ post result returned := by
  subst encoded
  obtain ⟨childFuel, final, values, invoked, confined, satisfied⟩ := holds.returning permitted normal
  obtain ⟨parentFuel, result, returned, resumed, finished⟩ :=
    continuation final values ⟨childFuel, invoked⟩ confined satisfied
  obtain ⟨fuel, composed⟩ := run_call_exists methodFound instructionFound stepped ⟨childFuel, invoked⟩
    ⟨parentFuel, resumed⟩
  exact ⟨fuel, result, returned, composed, finished⟩

/-- Continue after a callee whose contract names no exception into a caller path that raises. -/
theorem run_call_raises_after_outcome {Input Output : Type} {c : OutcomeContract Input Output} {program : CIL.Program}
    {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {exception : String}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated) (normal : c.raises input updated = none)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      RunRaises program method (pc + 1) args frame (values ++ rest) final exception) :
    RunRaises program method pc args frame stack memory exception := by
  subst encoded
  obtain ⟨childFuel, final, values, invoked, confined, satisfied⟩ := holds.returning permitted normal
  obtain ⟨parentFuel, fault, resumed, thrown⟩ := continuation final values ⟨childFuel, invoked⟩ confined satisfied
  have child := invoke_mono program childFuel parentFuel callee _ updated (.ok (final, values)) trivial invoked
  have parent := run_mono program parentFuel childFuel method (pc + 1) args frame _ final (.error fault)
    (by simp [Settled, thrown]) resumed
  rw [Nat.add_comm parentFuel childFuel] at parent
  exact ⟨childFuel + parentFuel + 1, fault, run_call_of_invoke methodFound instructionFound stepped child parent, thrown⟩

/-- `run_call_of_outcome` from a well-formed memory, with both call invariants supplied. -/
theorem run_call_of_outcome_formed {Input Output : Type} {c : OutcomeContract Input Output} {program : CIL.Program}
    {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated) (formed : memory.WellFormed)
    (normal : c.raises input updated = none)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) → final.WellFormed →
      StaticWorldPreserved program memory final →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      ∃ fuel result returned,
        run program fuel method (pc + 1) args frame (values ++ rest) final = .ok (result, returned) ∧
        post result returned) :
    ∃ fuel result returned,
      run program fuel method pc args frame stack memory = .ok (result, returned) ∧ post result returned :=
  run_call_of_outcome holds input methodFound instructionFound stepped encoded permitted normal
    fun final values ⟨fuel, invoked⟩ =>
      have kept := call_frame_invariants methodFound instructionFound stepped formed invoked
      continuation final values ⟨fuel, invoked⟩ kept.1 kept.2

/-- `run_call_raises_after_outcome` from a well-formed memory, with both call invariants supplied. -/
theorem run_call_raises_after_outcome_formed {Input Output : Type} {c : OutcomeContract Input Output} {program : CIL.Program}
    {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory} {exception : String}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped : step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated) (formed : memory.WellFormed)
    (normal : c.raises input updated = none)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) → final.WellFormed →
      StaticWorldPreserved program memory final →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      RunRaises program method (pc + 1) args frame (values ++ rest) final exception) :
    RunRaises program method pc args frame stack memory exception :=
  run_call_raises_after_outcome holds input methodFound instructionFound stepped encoded permitted normal
    fun final values ⟨fuel, invoked⟩ =>
      have kept := call_frame_invariants methodFound instructionFound stepped formed invoked
      continuation final values ⟨fuel, invoked⟩ kept.1 kept.2

/-- `exported` follows from `internal`: same encodings and outcome under a weaker pre; on return, covering footprint and implied post. -/
structure OutcomeContract.Refines {Input Output : Type} (internal exported : OutcomeContract Input Output) : Prop where
  args : ∀ input, exported.args input = internal.args input
  results : ∀ out, exported.results out = internal.results out
  pre : ∀ input initial, exported.pre input initial → internal.pre input initial
  raises : ∀ input initial, exported.pre input initial → exported.raises input initial = internal.raises input initial
  footprint : ∀ input initial, exported.pre input initial → exported.raises input initial = none →
    ∀ entry ∈ internal.footprint input, ∃ outer ∈ exported.footprint input, Within entry outer
  post : ∀ input initial final out, exported.pre input initial → exported.raises input initial = none →
    Confined (internal.footprint input) initial final → internal.post input initial final out →
    exported.post input initial final out

/-- A normal-contract refinement whose outcomes agree under the exported pre refines the outcome contracts. -/
theorem OutcomeContract.Refines.of_method {Input Output : Type} {internal exported : OutcomeContract Input Output}
    (refines : internal.toMethodContract.Refines exported.toMethodContract)
    (raises : ∀ input initial, exported.pre input initial → exported.raises input initial = internal.raises input initial) :
    internal.Refines exported :=
  ⟨refines.args, refines.results, refines.pre, raises, fun _ _ permitted _ => refines.footprint _ _ permitted,
    fun _ _ _ _ permitted _ => refines.post _ _ _ _ permitted⟩

theorem OutcomeContract.Refines.refl {Input Output : Type} (c : OutcomeContract Input Output) : c.Refines c :=
  .of_method (.refl c.toMethodContract) fun _ _ _ => rfl

theorem OutcomeContract.Refines.trans {Input Output : Type} {first middle last : OutcomeContract Input Output}
    (left : first.Refines middle) (right : middle.Refines last) : first.Refines last where
  args input := (right.args input).trans (left.args input)
  results out := (right.results out).trans (left.results out)
  pre _ _ permitted := left.pre _ _ (right.pre _ _ permitted)
  raises _ _ permitted := (right.raises _ _ permitted).trans (left.raises _ _ (right.pre _ _ permitted))
  footprint _ _ permitted normal entry member := by
    have between := right.pre _ _ permitted
    obtain ⟨inner, inside, within⟩ :=
      left.footprint _ _ between ((right.raises _ _ permitted).symm.trans normal) entry member
    obtain ⟨outer, contains, enclosed⟩ := right.footprint _ _ permitted normal inner inside
    exact ⟨outer, contains, within.trans enclosed⟩
  post _ _ _ _ permitted normal framed satisfied :=
    have between := right.pre _ _ permitted
    have inner := (right.raises _ _ permitted).symm.trans normal
    right.post _ _ _ _ permitted normal (framed.widen_within (left.footprint _ _ between inner))
      (left.post _ _ _ _ between inner framed satisfied)

/-- Derive an outcome contract from a proved one it refines; the method is neither unfolded nor executed. -/
theorem OutcomeContract.Holds.weaken {Input Output : Type} {internal exported : OutcomeContract Input Output}
    {program : CIL.Program} {method : Nat} (holds : internal.Holds program method)
    (refines : internal.Refines exported) : exported.Holds program method := by
  intro input initial permitted
  have outcome := holds input initial (refines.pre _ _ permitted)
  have agree := refines.raises _ _ permitted
  rw [refines.args]
  cases selected : exported.raises input initial with
  | some exception =>
    rw [selected] at agree
    rw [← agree] at outcome
    exact outcome
  | none =>
    rw [selected] at agree
    rw [← agree] at outcome
    obtain ⟨fuel, final, values, invoked, framed, out, encoded, satisfied⟩ := outcome
    refine ⟨fuel, final, values, invoked, framed.widen_within (refines.footprint _ _ permitted selected), out, ?_,
      refines.post _ _ _ _ permitted selected framed satisfied⟩
    rw [refines.results]; exact encoded

#print axioms OutcomeContract.Refines.trans
#print axioms OutcomeContract.Holds.weaken
#print axioms run_call_of_outcome_formed
#print axioms run_call_raises_after_outcome_formed
#print axioms run_call_error
#print axioms run_call_raises_after_outcome
#print axioms run_call_raises_of_contract
#print axioms run_call_of_outcome
#print axioms invoke_unique

/-- Step a `Raises` or `RunRaises` goal through checked instructions to a `throw`,
    leaving each `.call` for `cil_outcome_raise`. -/
syntax "cil_raise_steps_normalized" "[" term,* "]" : tactic

/-- One raising step on the fetched opcode: a `throw` raises here, any other op steps to the next pc. -/
syntax "cil_raise_run_step" "[" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_raise_run_step [$facts:term,*]) => withMainContext do
    let (methodSyntax, instructionSyntax, operation) ←
      cilFetchedOp ``CIL.Safety.run_next_raises some 4 facts.getElems
    evalTactic (← if operation == ``CIL.Op.throw then
        `(tactic| cil_strict exact CIL.Safety.run_throw_raises $methodSyntax $instructionSyntax rfl)
      else
        `(tactic| (
          cil_strict refine CIL.Safety.run_next_raises $methodSyntax $instructionSyntax
            (by cil_checked_step_normalized [$facts,*]) ?_
          cil_stack_cleanup)))

macro_rules
  | `(tactic| cil_raise_steps_normalized [$facts:term,*]) =>
  `(tactic| (
    try dsimp only [Nat.reduceAdd]
    cil_stack_cleanup
    try (cil_strict refine CIL.Safety.raises_of_run
           (by cil_lookup [$[$facts:term],*])
           (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl))
           (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl)) ?_)
    cil_steps_from "cil_raise_steps took no step: the method or instruction lookup, or the first step, did not close; pass the lookup hypothesis, feature facts or step facts"
      cil_raise_run_step [$[$facts:term],*]))

syntax "cil_raise_steps" "[" term,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cil_raise_steps [$facts:term,*]) => do
    let config ← `(Lean.Parser.Tactic.optConfig|)
    let prepared ← normaliseStepFacts config facts.getElems
    withMainContext <| evalTactic (← `(tactic| cil_raise_steps_normalized [$[$prepared:term],*]))

/-- At a `bind_call` site, continue past a callee whose contract names no exception for this
    input, in a returning or a raising caller goal, leaving the precondition, the `raises`
    equation and the continuation. -/
syntax "cil_outcome_call" term:max term:max " at " ident "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_outcome_call $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| first
    | refine CIL.Safety.run_call_raises_after_outcome $holds $input
        (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
        (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_ ?_
    | refine CIL.Safety.run_call_of_outcome $holds $input
        (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
        (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_ ?_)

/-- `cil_outcome_call` through the `_formed` theorems: leaves the precondition, the caller
    memory's `WellFormed`, the `raises` equation, then the continuation with both invariants. -/
syntax "cil_formed_outcome_call" term:max term:max " at " ident "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_formed_outcome_call $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| first
    | refine CIL.Safety.run_call_raises_after_outcome_formed $holds $input
        (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
        (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_ ?_ ?_
    | refine CIL.Safety.run_call_of_outcome_formed $holds $input
        (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
        (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_ ?_ ?_)

/-- At a `bind_call` site, propagate the exception the callee's contract names for this
    input, leaving the precondition and the `raises` equation. -/
syntax "cil_outcome_raise" term:max term:max " at " ident "[" term,* "]" : tactic

macro_rules
  | `(tactic| cil_outcome_raise $holds $input at $site:ident [$facts:term,*]) =>
  `(tactic| (
    refine CIL.Safety.run_call_raises_of_contract $holds $input
      (by cil_lookup [$[$facts:term],*]) $(Lean.mkIdent (site.getId ++ `call))
      (by cil_checked_step [$[$facts:term],*]) (by rfl)
      (by first | rfl | (simp [$[$facts:term],*] <;> (repeat constructor) <;> rfl)) ?_ ?_))

end CIL.Safety
