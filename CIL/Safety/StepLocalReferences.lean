import CIL.Safety.LocalReferences
import CIL.Safety.ExecutionFrameOwnership

/-!
# Steps preserve frame references

The references held in a frame's local slots stay valid across one checked step, including
a store that replaces a slot. Part of the per-step `LiveState` invariant.
-/

namespace CIL.Safety

theorem stored_frame_references_valid (m result : Memory) (frame : Frame) (index : Nat)
    (slot final : LocalSlot) (value : Value) (hm : m.WellFormed)
    (valid : frame.ReferencesValid m) (present : frame.locals[index]? = some slot)
    (h : storeLocal m slot value = .ok (final, result)) :
    Frame.ReferencesValid result { frame with locals := frame.locals.set index final } := by
  have retained := valid.preserve hm (storeLocal_extends_allocations _ _ _ _ _ h)
  have stored := storeLocal_preserves_reference_validity _ _ _ _ _ hm
    (valid.1 slot (List.mem_of_getElem? present)) h
  refine ⟨?_, retained.2⟩
  intro other member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact retained.1 other old
  · subst other
    exact stored

/-- A step keeps every frame slot reference valid in the memory it leaves behind. -/
theorem step_preserves_frame_references (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed) (valid : frame.ReferencesValid m)
    (h : step body operation pc args frame stack m = .ok action) :
    (action.frameAfter frame).ReferencesValid action.memory := by
  have effect := step_effect _ _ _ _ _ _ _ _ h
  have retained := valid.preserve hm effect.allocations
  generalize action.frameAfter frame = final, action.memory = result at effect retained ⊢
  cases effect with
  | stackAllocation effect => cases effect <;> exact retained
  | arrayAllocation | memory | valueHome | localHome => exact retained
  | store found stored => exact stored_frame_references_valid _ _ _ _ _ _ _ hm valid found stored

#print axioms stored_frame_references_valid
#print axioms step_preserves_frame_references

end CIL.Safety
