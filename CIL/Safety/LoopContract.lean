import CIL.Safety.LoopAutomation
import CIL.Safety.LoopVC
import CIL.Safety.MethodContract

/-!
# Loop termination and calls in loops

The induction principle for loop termination (an invariant with a decreasing measure), its
composition with frame entry into one theorem about `invoke` (`invoke_loop_induction`, and
`invoke_loop_satisfies` for any postcondition), and the rules that cross a call inside a loop
through the callee's `MethodContract`. The tactics that apply them are in
`CIL.Safety.LoopFrameSteps`.
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
    (continuation : ∀ final output,
      CallResult c program callee input updated final output →
      LoopTerminates program method args post ⟨pc + 1, frame, c.results output ++ rest, final⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  WP.adequate.mpr (run_call_of_contract holds input methodFound instructionFound stepped
    encoded permitted (fun final output result =>
      WP.adequate.mp (continuation final output result)))

/-- `loop_terminates_call` that also hands the continuation the callee's `WellFormed`, static
    world and catalog agreement. -/
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
    (continuation : ∀ final output,
      CallResult c program callee input updated final output →
      FrameInvariants program memory final →
      LoopTerminates program method args post ⟨pc + 1, frame, c.results output ++ rest, final⟩) :
    LoopTerminates program method args post ⟨pc, frame, stack, memory⟩ :=
  WP.adequate.mpr (run_call_of_contract_formed holds input methodFound instructionFound stepped
    encoded permitted formed (fun final output result invariants =>
      WP.adequate.mp (continuation final output result invariants)))

#print axioms loop_terminates_induction

/-- A checked frame entry whose first state terminates once every invariant loop head does, and an
    iteration that may assume termination from every invariant state of smaller measure, give a
    successful invocation returning `values` in a final memory that satisfies `kept`. The entry
    path steps to a loop head and applies its hypothesis there, so a store on the way may name
    the memory it produces; every continuing iteration must reach an invariant state of smaller
    measure, crossing a call with `loop_terminates_call`. -/
theorem invoke_loop_induction {α : Type} {program : CIL.Program} {method : Nat}
    {body : CIL.Method} {args : List Value} {memory entered : Memory} {frame : Frame}
    {values : List Value} {kept : Memory → Prop}
    (found : program[method]? = some body) (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (configuration : α → LoopState) (invariant : α → Prop) (measure : α → Nat)
    (entry : (∀ start, invariant start →
        LoopTerminates program method args
          (fun returned results => kept returned ∧ results = values) (configuration start)) →
      LoopTerminates program method args
        (fun returned results => kept returned ∧ results = values) ⟨0, frame, [], entered⟩)
    (progress : ∀ state, invariant state →
      (∀ next, invariant next → measure next < measure state →
        LoopTerminates program method args
          (fun returned results => kept returned ∧ results = values) (configuration next)) →
      LoopTerminates program method args
        (fun returned results => kept returned ∧ results = values) (configuration state)) :
    ∃ fuel final, invoke program fuel method args memory = .ok (final, values) ∧ kept final :=
  invoke_loop_results found checked setup (fun (_ : Unit) => ⟨0, frame, [], entered⟩)
    (fun _ => True) (fun _ => 0) () loop_reaches_refl trivial fun _ _ => .inl (entry
      (loop_terminates_induction program method args configuration invariant measure _ progress))
#print axioms invoke_loop_induction

/-- `invoke_loop_induction` for any postcondition on the final memory and results, so an
    `Ensures` goal takes it directly after its premises are introduced. The entry path steps to a
    loop head and applies its hypothesis there; every continuing iteration must reach an invariant
    state of smaller measure. -/
theorem invoke_loop_satisfies {α : Type} {program : CIL.Program} {method : Nat}
    {body : CIL.Method} {args : List Value} {memory entered : Memory} {frame : Frame}
    {post : Memory → List Value → Prop}
    (found : program[method]? = some body) (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (configuration : α → LoopState) (invariant : α → Prop) (measure : α → Nat)
    (entry : (∀ start, invariant start →
        LoopTerminates program method args post (configuration start)) →
      LoopTerminates program method args post ⟨0, frame, [], entered⟩)
    (progress : ∀ state, invariant state →
      (∀ next, invariant next → measure next < measure state →
        LoopTerminates program method args post (configuration next)) →
      LoopTerminates program method args post (configuration state)) :
    ∃ fuel final values, invoke program fuel method args memory = .ok (final, values) ∧
      post final values := by
  obtain ⟨fuel, ⟨final, values⟩, executed, satisfied⟩ :=
    entry (loop_terminates_induction program method args configuration invariant measure post
      progress)
  exact ⟨fuel, final, values, invoke_of_run found checked setup executed, satisfied⟩
#print axioms invoke_loop_satisfies

/-- A later loop, entered from `state`: once every invariant head of that loop terminates, which
    an iteration of smaller measure from each invariant state gives, the path from `state` need
    only reach one of those heads. A method's loops in sequence chain through it from the exit of
    each into the next. -/
theorem loop_terminates_then {α : Type} {program : CIL.Program} {method : Nat}
    {args : List Value} {post : Memory → List Value → Prop} {state : LoopState}
    (configuration : α → LoopState) (invariant : α → Prop) (measure : α → Nat)
    (reach : (∀ start, invariant start →
        LoopTerminates program method args post (configuration start)) →
      LoopTerminates program method args post state)
    (progress : ∀ current, invariant current →
      (∀ next, invariant next → measure next < measure current →
        LoopTerminates program method args post (configuration next)) →
      LoopTerminates program method args post (configuration current)) :
    LoopTerminates program method args post state :=
  reach (loop_terminates_induction program method args configuration invariant measure post
    progress)
#print axioms loop_terminates_then
#print axioms loop_terminates_call
#print axioms loop_terminates_call_formed

end CIL.Safety
