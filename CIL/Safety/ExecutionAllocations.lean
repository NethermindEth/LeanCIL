import CIL.Safety.ExecutionInvariants
import CIL.Safety.FrameOwnership

namespace CIL.Safety

set_option maxHeartbeats 800000

theorem checked_write_extends_allocations (m result : Memory) (r : Reference)
    (bytes : List (BitVec 8)) (alignment : Nat) (reference : ManagedReference) (width : Nat)
    (h : checkedAt reference width (write m r bytes alignment) = .ok result) :
    AllocationExtension m result := by
  exact write_extends_allocations _ _ _ _ _ (checkedAt_ok h)

theorem storeValue_extends_allocations (m result : Memory) (reference : ManagedReference)
    (value : CIL.Value) (h : storeValue m reference value = .ok result) :
    AllocationExtension m result := by
  exact (storeValue_effect _ _ _ _ h).allocations

theorem memoryInstruction_extends_allocations (operation : CIL.MemoryOp)
    (stack values : List Value) (m result : Memory)
    (h : memoryInstruction operation stack m = .ok (result, values)) :
    AllocationExtension m result := by
  exact (memoryInstruction_effect _ _ _ _ _ h).allocations

theorem instruction_extends_allocations (operation : CIL.Op) (stack values : List Value)
    (m result : Memory) (h : instruction operation stack m = .ok (result, values)) :
    AllocationExtension m result := by
  exact (instruction_effect _ _ _ _ _ h).allocations

theorem staticInstruction_extends_allocations (body : CIL.Method) (pc : Nat)
    (operation : CIL.MemoryOp) (stack values : List Value) (m result : Memory)
    (h : staticInstruction body pc operation stack m = .ok (result, values)) :
    AllocationExtension m result := by
  exact (staticInstruction_effect _ _ _ _ _ _ _ h).allocations

theorem step_extends_allocations (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (h : step body operation pc args frame stack m = .ok action) :
    AllocationExtension m action.memory := by
  exact (step_effect _ _ _ _ _ _ _ _ h).allocations

/-- Frame teardown changes lifetime flags, but never recycles an identity. -/
theorem leaveFrame_nextIdentity (frame : Frame) (m : Memory) :
    (leaveFrame frame m).nextIdentity = m.nextIdentity :=
  (expireAll_retained_fields frame.owned m).2.2.2

#print axioms step_extends_allocations

def Frame.OwnedAbove (frame : Frame) (watermark : Nat) : Prop :=
  ∀ id ∈ frame.owned, watermark ≤ id

def FrameAction.OwnedAbove (action : FrameAction) (watermark : Nat) : Prop :=
  match action with
  | .next _ _ frame _ | .construct _ _ _ frame _ _ _ => frame.OwnedAbove watermark
  | .call _ _ _ _ | .returned _ _ => True

theorem step_ownedAbove (body : CIL.Method) (operation : CIL.Op) (pc : Nat)
    (args : List Value) (frame : Frame) (stack : List Value) (m : Memory)
    (action : FrameAction) (watermark : Nat) (old : frame.OwnedAbove watermark)
    (bound : watermark ≤ m.nextIdentity)
    (h : step body operation pc args frame stack m = .ok action) :
    action.OwnedAbove watermark := by
  have effect := step_effect _ _ _ _ _ _ _ _ h
  have above : (action.frameAfter frame).OwnedAbove watermark := by
    generalize action.frameAfter frame = final, action.memory = result at effect ⊢
    cases effect with
    | memory | store => exact old
    | valueHome allocated _ | localHome allocated _ =>
      intro id member
      rcases List.mem_cons.mp member with rfl | member
      · exact (allocateHome_fresh _ _ _ _ _ allocated).2.1 ▸ bound
      · exact old id member
  cases action <;> first | exact above | trivial

#print axioms step_ownedAbove

end CIL.Safety
