import CIL.Safety.FrameAllocations
import CIL.Safety.StaticWorld

/-!
# Statics outlive frames

Readonly static storage is never owned by a frame, so tearing a frame down keeps every
static binding and the whole `StaticWorldValid` invariant.
-/

namespace CIL.Safety

/-- A frame never owns an immutable static allocation. -/
theorem frame_does_not_own_immutable (m : Memory) (frame : Frame)
    (owns : FrameAllocations m frame.activation frame.owned)
    (id : AllocationId) (a : Allocation) (present : m.allocations id = some a)
    (immutable : a.kind = .immutableStatic) : id ∉ frame.owned := by
  intro member
  obtain ⟨other, found, kind, _⟩ := owns id member
  have equal := Option.some.inj (found.symm.trans present)
  subst other
  rw [immutable] at kind
  cases kind

/-- Leaving a frame keeps a valid static binding valid. -/
theorem leaveFrame_preserves_static_binding (m : Memory) (frame : Frame)
    (owns : FrameAllocations m frame.activation frame.owned)
    (descriptor : CIL.StaticDescriptor) (reference : Reference)
    (valid : StaticBindingValid m descriptor reference) :
    StaticBindingValid (leaveFrame frame m) descriptor reference := by
  obtain ⟨offset, a, present, live, kind, size, bytes⟩ := valid
  have absent := frame_does_not_own_immutable _ _ owns _ _ present kind
  have lookup : (leaveFrame frame m).allocations reference.allocation =
      m.allocations reference.allocation := by
    simp [leaveFrame, expireAll_allocations, absent]
  have retained := expireAll_retained_fields frame.owned m
  refine ⟨offset, a, lookup.trans present, live, kind, size, ?_⟩
  rw [read_allocation_congr m (leaveFrame frame m) reference descriptor.bytes.length 1
    lookup retained.1 retained.2.1]
  exact bytes

/-- Leaving a frame preserves a valid static world. -/
theorem leaveFrame_preserves_static_world (descriptors : List CIL.StaticDescriptor)
    (m : Memory) (frame : Frame) (owns : FrameAllocations m frame.activation frame.owned)
    (world : StaticWorldValid descriptors m) :
    StaticWorldValid descriptors (leaveFrame frame m) := by
  have retained := expireAll_retained_fields frame.owned m
  refine ⟨world.1, world.2.1, ?_, ?_⟩
  · constructor
    · rw [show (leaveFrame frame m).staticBindings = m.staticBindings from retained.2.2.1]
      exact world.2.2.1.1
    · intro binding member
      rw [show (leaveFrame frame m).staticBindings = m.staticBindings from retained.2.2.1]
        at member
      obtain ⟨a, present, live, kind⟩ := world.2.2.1.2 binding member
      have absent := frame_does_not_own_immutable _ _ owns _ _ present kind
      refine ⟨a, ?_, live, kind⟩
      simpa [leaveFrame, expireAll_allocations, absent] using present
  · intro descriptor selected binding member key
    rw [show (leaveFrame frame m).staticBindings = m.staticBindings from retained.2.2.1] at member
    exact leaveFrame_preserves_static_binding _ _ owns _ _
      (world.2.2.2 descriptor selected binding member key)

#print axioms leaveFrame_preserves_static_world
end CIL.Safety
