import CIL.Safety.StepComposition
import CIL.Safety.CallComposition

/-!
# Total weakest preconditions for checked execution

`WP` hides the fuel and returned memory of a successful checked execution. It uses the existing
interpreter, including its argument checks, frame lifetime checks and located faults. Structural
rules compose checked instruction equations and separately proved calls without exposing fuel.
-/

namespace CIL.Safety

/-- Checked execution terminates successfully and its final memory and values satisfy `post`.
    Faults, including exhausted fuel, never establish this predicate. -/
def WP (execution : Nat → Except LocatedFault (Memory × List Value))
    (post : Memory → List Value → Prop) : Prop :=
  ∃ fuel final values, execution fuel = .ok (final, values) ∧ post final values

namespace WP

/-- A weakest precondition is exactly a finite checked execution with its postcondition. -/
theorem adequate {execution : Nat → Except LocatedFault (Memory × List Value)}
    {post : Memory → List Value → Prop} :
    WP execution post ↔
      ∃ fuel final values, execution fuel = .ok (final, values) ∧ post final values := Iff.rfl

#print axioms adequate

/-- Weakening the postcondition preserves the same successful checked execution. -/
theorem consequence {execution : Nat → Except LocatedFault (Memory × List Value)}
    {post weaker : Memory → List Value → Prop} (proof : WP execution post)
    (implies : ∀ memory values, post memory values → weaker memory values) :
    WP execution weaker := by
  obtain ⟨fuel, final, values, executed, satisfied⟩ := proof
  exact ⟨fuel, final, values, executed, implies final values satisfied⟩

#print axioms consequence

/-- A proved preservation property carries a memory assertion to the final memory. The
    preservation premise must account for writes and aliases; access alone is not content. -/
theorem frame {execution : Nat → Except LocatedFault (Memory × List Value)}
    {post : Memory → List Value → Prop} {assertion : Memory → Prop} {initial : Memory}
    (proof : WP execution post) (holds : assertion initial)
    (preserved : ∀ fuel final values, execution fuel = .ok (final, values) →
      assertion initial → assertion final) :
    WP execution (fun final values => post final values ∧ assertion final) := by
  obtain ⟨fuel, final, values, executed, satisfied⟩ := proof
  exact ⟨fuel, final, values, executed, satisfied, preserved fuel final values executed holds⟩

#print axioms frame

/-- An exact checked prefix transfers a successful suffix to its starting state. -/
theorem sequence {before after : Nat → Except LocatedFault (Memory × List Value)}
    {post : Memory → List Value → Prop} {cost : Nat}
    (segment : ∀ fuel, before (fuel + cost) = after fuel) (suffix : WP after post) :
    WP before post := by
  obtain ⟨fuel, final, values, executed, satisfied⟩ := suffix
  exact ⟨fuel + cost, final, values, (segment fuel).trans executed, satisfied⟩

#print axioms sequence

/-- One fetched instruction continues with the checked state it actually produces. -/
theorem step {program : CIL.Program} {method pc target : Nat}
    {body : CIL.Method} {operation : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body) (fetched : body.code[pc]? = some operation)
    (stepped : Safety.step body operation pc args frame stack memory =
      .ok (.next target values nextFrame updated))
    (rest : WP (fun fuel => run program fuel method target args nextFrame values updated) post) :
    WP (fun fuel => run program fuel method pc args frame stack memory) post :=
  run_next_exists post found fetched stepped rest

#print axioms step

/-- A checked return expires the frame and validates every value before establishing `post`. -/
theorem returned {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {operation : CIL.Op} {args stack values : List Value}
    {frame : Frame} {memory updated : Memory} {post : Memory → List Value → Prop}
    (found : program[method]? = some body) (fetched : body.code[pc]? = some operation)
    (stepped : Safety.step body operation pc args frame stack memory =
      .ok (.returned values updated))
    (checked : values.mapM (checkedValue (leaveFrame frame updated)) = .ok values)
    (satisfied : post (leaveFrame frame updated) values) :
    WP (fun fuel => run program fuel method pc args frame stack memory) post :=
  run_return_exists found fetched stepped checked satisfied

#print axioms returned

/-- Checked argument validation and actual frame allocation lift a body proof to invocation. -/
theorem enter {program : CIL.Program} {method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered : Memory}
    {post : Memory → List Value → Prop}
    (found : program[method]? = some body)
    (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (bodyProof : WP (fun fuel => run program fuel method 0 args frame [] entered) post) :
    WP (fun fuel => invoke program fuel method args memory) post :=
  invoke_exists_of_run found checked setup bodyProof

#print axioms enter

/-- Compose a checked call with its suffix, retaining the helper's complete postcondition. -/
theorem call {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method}
    {operation : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory}
    {helperPost post : Memory → List Value → Prop}
    (found : program[method]? = some body) (fetched : body.code[pc]? = some operation)
    (stepped : Safety.step body operation pc args frame stack memory =
      .ok (.call callee arguments rest updated))
    (helper : WP (fun fuel => invoke program fuel callee arguments updated) helperPost)
    (suffix : ∀ final values, helperPost final values →
      WP (fun fuel => run program fuel method (pc + 1) args frame (values ++ rest) final) post) :
    WP (fun fuel => run program fuel method pc args frame stack memory) post := by
  obtain ⟨childFuel, middle, output, invoked, helperResult⟩ := helper
  exact run_call_post found fetched stepped ⟨childFuel, invoked⟩
    (suffix middle output helperResult)

#print axioms call

end WP
end CIL.Safety
