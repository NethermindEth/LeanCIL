import CIL.Safety.ExecutionInvariants
import CIL.Safety.FrameOwnership

/-!
# Steps only extend the allocation table

Checked writes, value stores, instructions and whole steps each yield an
`AllocationExtension`: no existing allocation changes its lifetime or layout, and identities
are never reused. Teardown is the one exception, handled in `ExecutionLifetime`. The
watermark predicates `OwnedAbove` record that a frame owns only allocations made after a
given identity, which `ExecutionLifetime` uses to protect a caller's storage.
-/

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

/-- Every allocation the frame owns has an identity at or above `watermark`, so none of them
    existed when the watermark was taken. -/
def Frame.OwnedAbove (frame : Frame) (watermark : Nat) : Prop :=
  ∀ id ∈ frame.owned, watermark ≤ id

/-- `Frame.OwnedAbove` for the frame an action continues in; calls and returns carry no
    frame and impose nothing. -/
def FrameAction.OwnedAbove (action : FrameAction) (watermark : Nat) : Prop :=
  match action with
  | .next _ _ frame _ | .construct _ _ _ frame _ _ _ => frame.OwnedAbove watermark
  | .call _ _ _ _ | .returned _ _ => True

/-- A step keeps the current frame above a watermark that memory has already passed: any home
    it allocates gets a fresh identity. -/
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
    | stackAllocation effect =>
      cases effect with
      | empty => exact old
      | fresh allocated _ =>
        intro id member
        rcases List.mem_cons.mp member with rfl | member
        · exact (allocateHome_fresh _ _ _ _ _ allocated).2.1 ▸ bound
        · exact old id member
    | memory | store => exact old
    | valueHome allocated _ | localHome allocated _ =>
      intro id member
      rcases List.mem_cons.mp member with rfl | member
      · exact (allocateHome_fresh _ _ _ _ _ allocated).2.1 ▸ bound
      · exact old id member
  cases action <;> first | exact above | trivial

#print axioms step_ownedAbove

end CIL.Safety
