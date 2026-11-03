import CIL.Safety.LoopAutomation
import CIL.Safety.LoopVC
import CIL.Safety.MethodContract

/-!
# Loop termination and calls in loops

The induction principle for loop termination (an invariant with a decreasing measure), its
composition with frame entry into one theorem about `invoke` (`invoke_loop_induction`), and the
rules that cross a call inside a loop through the callee's `MethodContract`, plus the tactics
`cil_loop_advance` and `cil_loop_call` that apply them to fetched instructions.
-/

namespace CIL.Safety

/-- An invariant and a decreasing measure give termination; each iteration may assume it for
    every smaller invariant state. -/
theorem loop_terminates_induction {α : Type} (program : CIL.Program) (method : Nat)
    (args : List Value) (configuration : α → LoopState) (invariant : α → Prop) (measure : α → Nat)
    (post : Memory → List Value → Prop)
    (progress : ∀ state, invariant state →
      (∀ next, invariant next → measure next < measure state →
        LoopTerminates program method args post (configuration next)) →
      LoopTerminates program method args post (configuration state))
    (state : α) (valid : invariant state) :
    LoopTerminates program method args post (configuration state) := by
  generalize rank : measure state = n
  induction n using Nat.strongRecOn generalizing state with
  | ind n ih =>
    exact progress state valid fun next preserved decreases =>
      ih (measure next) (by omega) next preserved rfl

/-- A loop path crosses a fetched call through the callee's contract, never its body or
    fuel. -/
theorem loop_terminates_call {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value} {frame : Frame} {memory updated : Memory}
    {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      LoopTerminates program method args post ⟨pc + 1, frame, values ++ rest, final⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  run_call_of_contract holds input methodFound instructionFound stepped encoded permitted
    continuation

/-- `loop_terminates_call` that also hands the continuation the callee's `WellFormed` and
    static world. -/
theorem loop_terminates_call_formed {Input Output : Type} {c : MethodContract Input Output}
    {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method} {op : CIL.Op}
    {args stack arguments rest : List Value} {frame : Frame} {memory updated : Memory}
    {post : Memory → List Value → Prop}
    (holds : c.Holds program callee) (input : Input)
    (methodFound : program[method]? = some body) (instructionFound : body.code[pc]? = some op)
    (stepped :
      step body op pc args frame stack memory = .ok (.call callee arguments rest updated))
    (encoded : arguments = c.args input) (permitted : c.pre input updated)
    (formed : memory.WellFormed)
    (continuation : ∀ final values,
      (∃ fuel, invoke program fuel callee arguments updated = .ok (final, values)) →
      final.WellFormed →
      StaticWorldPreserved program memory final →
      Confined (c.footprint input) updated final → c.Returns input updated final values →
      LoopTerminates program method args post ⟨pc + 1, frame, values ++ rest, final⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  run_call_of_contract_formed holds input methodFound instructionFound stepped encoded permitted
    formed continuation

#print axioms loop_terminates_induction

/-- A checked frame entry, a checked path to the first loop head where the invariant holds, and an
    iteration that may assume termination from every invariant state of smaller measure give a
    successful invocation returning `values` in a final memory that satisfies `kept`. An
    iteration that calls a method crosses it with `loop_terminates_call`; every continuing
    iteration must reach an invariant state of smaller measure. -/
theorem invoke_loop_induction {α : Type} {program : CIL.Program} {method : Nat}
    {body : CIL.Method} {args : List Value} {memory entered : Memory} {frame : Frame}
    {values : List Value} {kept : Memory → Prop}
    (found : program[method]? = some body) (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (configuration : α → LoopState) (invariant : α → Prop) (measure : α → Nat) (start : α)
    (path : LoopReaches program method args ⟨0, frame, [], entered⟩ (configuration start))
    (initial : invariant start)
    (progress : ∀ state, invariant state →
      (∀ next, invariant next → measure next < measure state →
        LoopTerminates program method args
          (fun returned results => kept returned ∧ results = values) (configuration next)) →
      LoopTerminates program method args
        (fun returned results => kept returned ∧ results = values) (configuration state)) :
    ∃ fuel final, invoke program fuel method args memory = .ok (final, values) ∧ kept final :=
  invoke_loop_results found checked setup configuration invariant measure start path initial
    fun state valid => .inl (loop_terminates_induction program method args configuration invariant
      measure _ progress state valid)
#print axioms invoke_loop_induction
#print axioms loop_terminates_call
#print axioms loop_terminates_call_formed

/-- Step a `LoopTerminates` goal through fetched instructions up to the next call or return,
    with the optional facts and those `gatherLoopFacts` finds. Any other instruction it cannot
    step fails, naming the pc, the instruction and the residual step. -/
syntax "cil_loop_advance" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| cil_loop_advance $[[$facts:term,*]]?) => do
    let facts ← gatherLoopFacts (facts.map (·.getElems) |>.getD #[])
    let prepared ← normaliseStepFacts (← `(Lean.Parser.Tactic.optConfig|))
      (#[← `(CIL.truth)] ++ facts)
    loopSteps "cil_loop_advance" .advance facts prepared

/-- Apply `holds`, the callee's contract at `input`, at the fetched loop call or at a
    `bind_call` site, with the optional facts and those `gatherLoopFacts` finds; leaves `pre`,
    then the continuation. Fails naming the pc and instruction when the goal is not at a call,
    and the residual when the call's arguments are not the contract's. -/
syntax "cil_loop_call" term:max term:max (" at " ident)? (" [" term,* "]")? : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| cil_loop_call $holds $input $[at $site:ident]? $[[$facts:term,*]]?) => do
    let facts ← gatherLoopFacts (facts.map (·.getElems) |>.getD #[])
    let instruction : Term ← match site with
      | some site => pure ⟨(mkIdent (site.getId ++ `call)).raw⟩
      | none => `(by cil_lookup [$[$facts:term],*])
    let saved ← saveState
    try
      Term.withoutErrToSorry <| withoutRecover <|
        evalTactic (← `(tactic| refine CIL.Safety.loop_terminates_call $holds $input
          (by cil_lookup [$[$facts:term],*]) $instruction
          (by cil_checked_step [$[$facts:term],*]) (by rfl) ?_ ?_))
    catch error =>
      saved.restore
      withMainContext do
        let some (source, _) ← loopGoalStates (← getMainTarget)
          | throwError "cil_loop_call: expected a `LoopTerminates` goal"
        let some parts ← loopStateParts? source | throw error
        let some position ← literalNat? parts[0]! | throw error
        let fetched ← observing? (loopFetch facts)
        saved.restore
        let some (op, _) := fetched
          | throwError "cil_loop_call: cannot fetch the instruction at pc {position}"
        unless (← whnfR op).isAppOf ``CIL.Op.call do
          throwError "cil_loop_call: pc {position} is {op}, not a call; step to the call first \
            with `cil_loop_advance`"
        throwError "cil_loop_call: the call at pc {position} ({op}) does not take the contract's \
          arguments for this input, or is not the named site:{indentD error.toMessageData}"

end CIL.Safety
