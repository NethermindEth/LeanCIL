import CIL.Safety.ExecutionLifetime
import CIL.Safety.FrameAllocations

/-!
# Frames keep owning their allocations

The current frame's owned allocations stay live frame allocations of its activation across a
checked step, and across a whole child run. Together with `ExecutionStaticWorld` this lets
invariants over a frame survive nested calls.
-/

namespace CIL.Safety

/-- A step keeps every allocation the resulting frame owns live and tagged with its activation,
    including a home the step just allocated. -/
theorem step_preserves_frame_allocations (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (hm : m.WellFormed)
    (owns : FrameAllocations m frame.activation frame.owned)
    (h : step body operation pc args frame stack m = .ok action) :
    FrameAllocations action.memory (action.frameAfter frame).activation
      (action.frameAfter frame).owned := by
  have effect := step_effect _ _ _ _ _ _ _ _ h
  have bounds : ∀ id ∈ frame.owned, id < m.nextIdentity := by
    intro id member
    obtain ⟨a, present, _, _⟩ := owns id member
    exact (hm.1 _ _ present).1
  have retained := owns.preserve effect.allocations bounds
  generalize action.frameAfter frame = final, action.memory = result at effect retained ⊢
  cases effect with
  | stackAllocation effect =>
    cases effect with
    | empty => exact retained
    | fresh allocated initialized =>
      rename_i reference allocatedMemory size reserved
      have fresh := allocateHome_fresh _ _ _ _ _ allocated
      have new := allocateHome_owned _ _ _ _ _ allocated
      have ext : AllocationExtension allocatedMemory result := by
        rcases initialized with rfl | written
        · exact .refl _
        · exact write_extends_allocations _ _ _ _ _ written
      have new := new.preserve ext (by
        intro id member
        obtain rfl := List.mem_singleton.mp member
        exact fresh.2.2)
      intro id member
      rcases List.mem_cons.mp member with rfl | member
      · exact new _ (by simp)
      · exact retained id member
  | memory | store => exact retained
  | valueHome allocated stored | localHome allocated stored =>
    have fresh := allocateHome_fresh _ _ _ _ _ allocated
    have new := (allocateHome_owned _ _ _ _ _ allocated).preserve (by
      first
      | exact (storeValue_effect _ _ _ _ stored).allocations
      | exact storeLocal_extends_allocations _ _ _ _ _ stored)
      (by intro id member; obtain rfl := List.mem_singleton.mp member; exact fresh.2.2)
    intro id member
    rcases List.mem_cons.mp member with rfl | member
    · exact new _ (by simp)
    · exact retained id member

/-- A child's whole run, from frame entry to its final memory, leaves the parent frame's
    allocations live. -/
theorem child_run_preserves_parent_frame (program : CIL.Program) (fuel method : Nat)
    (body : CIL.Method) (args values : List Value) (child parent : Frame)
    (m entered final : Memory) (hm : m.WellFormed)
    (owns : FrameAllocations m parent.activation parent.owned)
    (setup : enterFrame body args m = .ok (child, entered))
    (finish : run program fuel method 0 args child [] entered = .ok (final, values)) :
    FrameAllocations final parent.activation parent.owned := by
  apply owns.preserve (entered_run_preserves_caller_allocations _ _ _ _ _ _ _ _ _ _ setup finish)
  intro id member
  obtain ⟨a, present, _, _⟩ := owns id member
  exact (hm.1 _ _ present).1

#print axioms step_preserves_frame_allocations
#print axioms child_run_preserves_parent_frame

end CIL.Safety
