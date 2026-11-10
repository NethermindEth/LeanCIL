import CIL.Safety.StepComposition
import CIL.Safety.CallComposition

/-!
# Total weakest preconditions for checked execution

`WP` hides the budget and result of a checked execution relation. Successful returns use
`Execution`; exact prefixes use a relation retaining every continuation budget and located fault.
Structural rules compose existing interpreter proofs without introducing another interpreter.
-/

namespace CIL.Safety

/-- A single finite budget and result establish the execution relation and its postcondition.
    Any universal continuation budget in `execution` remains inside this existential budget. -/
def WP {α : Type} (execution : Nat → α → Prop) (post : α → Prop) : Prop :=
  ∃ cost result, execution cost result ∧ post result

/-- The successful-result relation of the existing checked interpreter. Errors, including
    fuel exhaustion, do not produce a result in this relation. -/
def Execution (execution : Nat → Except LocatedFault (Memory × List Value)) :
    Nat → (Memory × List Value) → Prop := fun fuel result => execution fuel = .ok result

namespace WP

/-- A weakest precondition is exactly a finite checked execution with its postcondition. -/
theorem adequate {execution : Nat → Except LocatedFault (Memory × List Value)}
    {post : (Memory × List Value) → Prop} :
    WP (Execution execution) post ↔
      ∃ fuel final values, execution fuel = .ok (final, values) ∧ post (final, values) := by
  constructor
  · rintro ⟨fuel, ⟨final, values⟩, executed, satisfied⟩
    exact ⟨fuel, final, values, executed, satisfied⟩
  · rintro ⟨fuel, final, values, executed, satisfied⟩
    exact ⟨fuel, (final, values), executed, satisfied⟩

#print axioms adequate

/-- Eliminate a successful WP into the interpreter's curried result convention. Applying this
    rule to a raw execution goal infers its postcondition without restating returned values. -/
theorem exists_execution {execution : Nat → Except LocatedFault (Memory × List Value)}
    {post : Memory → List Value → Prop}
    (proof : WP (Execution execution) (Function.uncurry post)) :
    ∃ fuel final values, execution fuel = .ok (final, values) ∧ post final values :=
  adequate.mp proof

#print axioms exists_execution

/-- An exact-result postcondition retains precisely one finite execution budget. -/
theorem exact_iff {α : Type} {execution : Nat → α → Prop} {target : α} :
    WP execution (fun result => result = target) ↔ ∃ cost, execution cost target := by
  constructor
  · rintro ⟨cost, result, ran, rfl⟩
    exact ⟨cost, ran⟩
  · rintro ⟨cost, ran⟩
    exact ⟨cost, target, ran, rfl⟩

#print axioms exact_iff

/-- Weakening the postcondition preserves the same budget and execution relation. -/
theorem consequence {α : Type} {execution : Nat → α → Prop}
    {post weaker : α → Prop} (proof : WP execution post)
    (implies : ∀ result, post result → weaker result) :
    WP execution weaker := by
  obtain ⟨cost, result, executed, satisfied⟩ := proof
  exact ⟨cost, result, executed, implies result satisfied⟩

#print axioms consequence

/-- A proved preservation property carries an assertion to the result. For memory assertions,
    preservation must account for writes and aliases; access alone is not content. -/
theorem frame {α : Type} {execution : Nat → α → Prop}
    {post assertion : α → Prop} {initial : α}
    (proof : WP execution post) (holds : assertion initial)
    (preserved : ∀ cost result, execution cost result → assertion initial → assertion result) :
    WP execution (fun result => post result ∧ assertion result) := by
  obtain ⟨cost, result, executed, satisfied⟩ := proof
  exact ⟨cost, result, executed, satisfied, preserved cost result executed holds⟩

#print axioms frame

/-- Sequential composition adds the two finite budgets using the supplied relation law.
    The law must preserve the full execution relation, including every prefix continuation. -/
theorem sequence {α β : Type} {first : Nat → α → Prop} {next : α → Nat → β → Prop}
    {combined : Nat → β → Prop} {middle : α → Prop} {post : β → Prop}
    (firstProof : WP first middle) (suffix : ∀ state, middle state → WP (next state) post)
    (compose : ∀ firstCost secondCost state result,
      first firstCost state → next state secondCost result →
      combined (firstCost + secondCost) result) : WP combined post := by
  obtain ⟨firstCost, state, ran, valid⟩ := firstProof
  obtain ⟨secondCost, result, continued, satisfied⟩ := suffix state valid
  exact ⟨firstCost + secondCost, result, compose _ _ _ _ ran continued, satisfied⟩

#print axioms sequence

/-- An exact checked prefix preserves a successful suffix without changing its result. -/
theorem of_prefix {before after : Nat → Except LocatedFault (Memory × List Value)}
    {post : (Memory × List Value) → Prop} {cost : Nat}
    (segment : ∀ fuel, before (fuel + cost) = after fuel)
    (suffix : WP (Execution after) post) : WP (Execution before) post := by
  obtain ⟨fuel, result, executed, satisfied⟩ := suffix
  exact ⟨fuel + cost, result, (segment fuel).trans executed, satisfied⟩

#print axioms of_prefix

/-- One fetched instruction continues with the checked state it actually produces. -/
theorem step {program : CIL.Program} {method pc target : Nat}
    {body : CIL.Method} {operation : CIL.Op} {args stack values : List Value}
    {frame nextFrame : Frame} {memory updated : Memory} {post : (Memory × List Value) → Prop}
    (found : program[method]? = some body) (fetched : body.code[pc]? = some operation)
    (stepped : Safety.step body operation pc args frame stack memory =
      .ok (.next target values nextFrame updated))
    (rest : WP (Execution (fun fuel =>
      run program fuel method target args nextFrame values updated)) post) :
    WP (Execution (fun fuel => run program fuel method pc args frame stack memory))
      post :=
  adequate.mpr (run_next_exists (fun final values => post (final, values)) found fetched stepped
    (adequate.mp rest))

#print axioms step

/-- A checked return expires the frame and validates every value before establishing `post`. -/
theorem returned {program : CIL.Program} {method pc : Nat}
    {body : CIL.Method} {operation : CIL.Op} {args stack values : List Value}
    {frame : Frame} {memory updated : Memory} {post : (Memory × List Value) → Prop}
    (found : program[method]? = some body) (fetched : body.code[pc]? = some operation)
    (stepped : Safety.step body operation pc args frame stack memory =
      .ok (.returned values updated))
    (checked : values.mapM (checkedValue (leaveFrame frame updated)) = .ok values)
    (satisfied : post (leaveFrame frame updated, values)) :
    WP (Execution (fun fuel => run program fuel method pc args frame stack memory))
      post :=
  adequate.mpr (run_return_exists found fetched stepped checked satisfied)

#print axioms returned

/-- Checked argument validation and actual frame allocation lift a body proof to invocation. -/
theorem enter {program : CIL.Program} {method : Nat} {body : CIL.Method}
    {args : List Value} {frame : Frame} {memory entered : Memory}
    {post : (Memory × List Value) → Prop}
    (found : program[method]? = some body)
    (checked : args.mapM (checkedValue memory) = .ok args)
    (setup : enterFrame body args memory = .ok (frame, entered))
    (bodyProof : WP (Execution (fun fuel => run program fuel method 0 args frame [] entered))
      post) :
    WP (Execution (fun fuel => invoke program fuel method args memory)) post :=
  adequate.mpr (invoke_exists_of_run found checked setup (adequate.mp bodyProof))

#print axioms enter

/-- Compose a checked call with its suffix, retaining the helper's complete postcondition. -/
theorem call {program : CIL.Program} {method pc callee : Nat} {body : CIL.Method}
    {operation : CIL.Op} {args stack arguments rest : List Value}
    {frame : Frame} {memory updated : Memory}
    {helperPost post : (Memory × List Value) → Prop}
    (found : program[method]? = some body) (fetched : body.code[pc]? = some operation)
    (stepped : Safety.step body operation pc args frame stack memory =
      .ok (.call callee arguments rest updated))
    (helper : WP (Execution (fun fuel => invoke program fuel callee arguments updated))
      helperPost)
    (suffix : ∀ final values, helperPost (final, values) →
      WP (Execution (fun fuel =>
        run program fuel method (pc + 1) args frame (values ++ rest) final))
        post) :
    WP (Execution (fun fuel => run program fuel method pc args frame stack memory))
      post := by
  obtain ⟨childFuel, ⟨middle, output⟩, invoked, helperResult⟩ := helper
  exact adequate.mpr (run_call_post found fetched stepped ⟨childFuel, invoked⟩
    (adequate.mp (suffix middle output helperResult)))

#print axioms call

end WP
end CIL.Safety
