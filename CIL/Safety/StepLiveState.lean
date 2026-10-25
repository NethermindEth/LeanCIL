import CIL.Safety.LiveState
import CIL.Safety.StepValues
import CIL.Safety.StepLocalReferences

/-!
# Steps preserve the live state

One checked step from a `LiveState` lands in a valid state for whatever it does next: the
same frame for `next` and `returned`, or a valid parent state plus valid child arguments
for `call` and `construct`. This is the per-step invariant whole-run safety proofs induct
over.
-/

namespace CIL.Safety

/-- A checked instruction preserves the current state or supplies a live child
    argument list and the parent's suspended state. Return is still checked
    again by run after expiration of private storage. -/
def FrameAction.StateValid (program : CIL.Program) (args : List Value) (current : Frame) :
    FrameAction → Prop
  | .next _ values frame memory => LiveState program args frame values memory
  | .call _ childArgs rest memory =>
    LiveState program args current rest memory ∧ ValuesValid memory childArgs
  | .construct _ childArgs rest frame _ _ memory =>
    LiveState program args frame rest memory ∧ ValuesValid memory childArgs
  | .returned values memory => LiveState program args current values memory

/-- A successful step from a live state yields a state valid for its action. -/
theorem step_live_state (program : CIL.Program) (method : Nat) (body : CIL.Method)
    (operation : CIL.Op) (pc : Nat) (args : List Value) (frame : Frame) (stack : List Value)
    (m : Memory) (action : FrameAction) (state : LiveState program args frame stack m)
    (found : program[method]? = some body)
    (h : step body operation pc args frame stack m = .ok action) :
    action.StateValid program args frame := by
  have contract := step_contract _ _ _ _ _ _ _ _ h
  have ext := contract.effect.allocations
  have memory := contract.effect.wellFormed state.memory
  have arguments := state.arguments.preserve state.memory ext
  have values := contract.values state.memory state.stack
  have references :=
    step_preserves_frame_references _ _ _ _ _ _ _ _ state.memory state.references h
  have owned := step_preserves_frame_allocations _ _ _ _ _ _ _ _ state.memory state.owned h
  have statics := step_preserves_static_world _ _ _ _ _ _ _ _ _ state.memory
    (program_static_sites_valid _ _ _ found) state.statics h
  cases action with
  | next target stack' frame' updated =>
    exact ⟨memory, arguments, values, references, owned, statics⟩
  | returned result updated => exact ⟨memory, arguments, values, references, owned, statics⟩
  | call callee childArgs rest updated =>
    exact ⟨⟨memory, arguments, values.2, references, owned, statics⟩, values.1⟩
  | construct callee childArgs rest frame' temporary kind updated =>
    exact ⟨⟨memory, arguments, values.2, references, owned, statics⟩, values.1⟩

theorem programStep_live_state {program : CIL.Program} {method pc : Nat}
    {args : List Value} {frame : Frame} {stack : List Value} {m : Memory} {action : FrameAction}
    (step : ProgramStep program method pc args frame stack m action)
    (state : LiveState program args frame stack m) : action.StateValid program args frame := by
  obtain ⟨body, operation, found, _, success⟩ := step
  exact step_live_state _ _ _ _ _ _ _ _ _ _ state found success

#print axioms step_live_state
#print axioms programStep_live_state

end CIL.Safety
